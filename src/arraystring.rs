//! [`ArrayVec`](../tinyvec/struct.ArrayVec.html) backed strings
use crate::tinyvec::{Array, ArrayVec};

use core::{
	convert::{TryFrom, TryInto},
	fmt,
	hash::{Hash, Hasher},
	iter::{DoubleEndedIterator, FromIterator, FusedIterator},
	ops::{
		self, Add, AddAssign, Bound, Deref, DerefMut, Index, IndexMut,
		RangeBounds,
	},
	ptr,
	str::{self, Chars, FromStr, Utf8Error},
};

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String};

/// A UTF-8 encoded, fixed-capacity string.
///
/// An `ArrayString` is similar to [`String`], but is backed by an
/// [`ArrayVec`] instead of a [`Vec`]. This means it has similar
/// characteristics to `ArrayVec`:
/// * An `ArrayString` has a fixed capacity (in bytes), the size of the backing
///   array.
/// * An `ArrayString` has a dynamic length; characters can be added and
///   removed. Attempting to add characters when the capacity has been reached
///   will cause a panic.
///
/// Like `String`, the contents of an `ArrayString` must be valid UTF-8 at all
/// times.
///
/// `ArrayString` is intended to replicate the API of `String` as much as
/// possible. Like `ArrayVec`, some methods cannot be implemented, like
/// `from_raw_parts` or `reserve`
///
/// # Examples
/// Creating `ArrayString`s with [`TryFrom`]:
/// ```
/// # use tinyvec_string::ArrayString;
/// use std::convert::TryFrom;
/// // explicitly specifying the backing array type with a turbofish
/// // note that `try_from` fails if the backing array is not large enough
/// // to contain the string contents
/// let s1 = ArrayString::<[u8; 13]>::try_from("Hello, world!").unwrap();
///
/// assert_eq!(s1, "Hello, world!");
///
/// // annotate the variable type to specify the backing array
/// let s2: ArrayString<[u8; 13]> = ArrayString::try_from("Hello, world!").unwrap();
///
/// assert_eq!(s1, s2);
///
/// // `collect` (which uses `FromIterator`) will panic if the backing array
/// // is not large enough
/// let s3: ArrayString<[u8; 12]> =
///     vec!["foo", "bar", "baz"].into_iter().collect();
///
/// assert_eq!(s3, "foobarbaz");
/// ```
///
/// Creating `ArrayString`s with the [`from`] convenience method:
/// ```
/// # use tinyvec_string::ArrayString;
/// // this panics on capacity overflow
/// let s = ArrayString::<[u8; 6]>::from("foobar");
/// ```
///
/// [`String`]: https://doc.rust-lang.org/std/string/struct.String.html
/// [`ArrayVec`]: ../tinyvec/struct.ArrayVec.html
/// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
/// [`TryFrom`]: https://doc.rust-lang.org/std/convert/trait.TryFrom.html
/// [`from`]: #method.from
#[derive(Default, Copy, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct ArrayString<A: Array<Item = u8>> {
	vec: ArrayVec<A>,
}

impl<A: Array<Item = u8> + Default> ArrayString<A> {
	/// Creates a new empty `ArrayString`.
	///
	/// This creates a new [`ArrayVec`] with a backing array type `A` using its
	/// `Default` implementation (which should fill the array with zeroes).
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// // create an `ArrayString` with 16 bytes of capacity
	/// let s = ArrayString::<[u8; 16]>::new();
	/// ```
	///
	/// [`ArrayVec`]: ../tinyvec/struct.ArrayVec.html
	#[inline]
	pub fn new() -> ArrayString<A> {
		Self::default()
	}

	/// Creates a new `ArrayString` from another string type.
	///
	/// This can be used to create an `ArrayString` from any type with an
	/// applicable [`TryFrom`] implementation:
	/// * `&str`
	/// * `&mut str`
	/// * `char`
	/// * `&char`
	/// * `String`
	/// * `&String`
	/// * `Cow<str>`
	///
	/// [`TryFrom`]: https://doc.rust-lang.org/std/convert/trait.TryFrom.html
	///
	/// Because it relies on `TryFrom`, this method may panic (which is why it
	/// is not a `From` implementation).
	///
	/// # Panics
	/// Panics if the input string is larger than the backing array.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 13]>::from("Hello, world!");
	///
	/// assert_eq!(s, "Hello, world!");
	/// ```
	///
	/// This method panics when the string is too large:
	/// ```should_panic
	/// # use tinyvec_string::ArrayString;
	/// // the following line will panic!
	/// let s = ArrayString::<[u8; 10]>::from("This is quite a long string");
	/// ```
	pub fn from<S>(s: S) -> Self
	where
		S: fmt::Debug,
		Self: TryFrom<S, Error = CapacityOverflowError<S>>,
	{
		s.try_into().expect("Failed to convert into ArrayString")
	}
}

impl<A: Array<Item = u8>> ArrayString<A> {
	/// Converts a vector of bytes to an `ArrayString`.
	///
	/// `ArrayString` is backed by `ArrayVec`, so after ensuring valid UTF-8,
	/// this function simply constructs an `ArrayString` containing the
	/// provided `ArrayVec`.
	///
	/// The inverse of this method is [`into_bytes`].
	///
	/// # Errors
	///
	/// Returns `Err` if the slice is not UTF-8 with a description as to why the
	/// provided bytes are not UTF-8. The vector you moved in is also included.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	/// // some bytes, in a vector
	/// let ferris: ArrayVec<[u8; 7]> = array_vec![240, 159, 166, 128, 226, 153, 165];
	///
	/// // We know these bytes are valid UTF-8, so we'll use `unwrap()`.
	/// let ferris = ArrayString::from_utf8(ferris).unwrap();
	///
	/// assert_eq!("🦀♥", ferris);
	/// ```
	///
	/// Incorrect bytes:
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	///
	/// // some invalid bytes, in a vector
	/// let ferris: ArrayVec<[u8; 7]> = array_vec![0, 159, 166, 128, 226, 153, 165];
	///
	/// assert!(ArrayString::from_utf8(ferris).is_err());
	/// ```
	///
	/// See the docs for [`FromUtf8Error`] for more details on what you can do
	/// with this error.
	///
	/// [`into_bytes`]: struct.ArrayString.html#method.into_bytes
	/// [`FromUtf8Error`]: struct.FromUtf8Error.html
	#[inline]
	pub fn from_utf8(
		vec: ArrayVec<A>,
	) -> Result<ArrayString<A>, FromUtf8Error<A>> {
		match str::from_utf8(&vec) {
			Ok(..) => Ok(ArrayString { vec }),
			Err(error) => Err(FromUtf8Error { vec, error }),
		}
	}

	/// Converts a vector of bytes to an `ArrayString` without checking that
	/// the string contains valid UTF-8.
	///
	/// See the safe version, [`from_utf8`], for more details.
	///
	/// [`from_utf8`]: struct.ArrayString.html#method.from_utf8
	///
	/// # Safety
	///
	/// This function is unsafe because it does not check that the bytes passed
	/// to it are valid UTF-8. If this constraint is violated, it may cause
	/// memory unsafety issues with future users of the `String`, as the rest of
	/// the standard library assumes that `String`s are valid UTF-8.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	/// // some bytes, in a vector
	/// let ferris: ArrayVec<[u8; 7]> = array_vec![240, 159, 166, 128, 226, 153, 165];
	///
	/// let ferris = unsafe {
	/// 	// we know these bytes are valid UTF-8, so this is sound.
	///		ArrayString::from_utf8_unchecked(ferris)
	/// };
	///
	/// assert_eq!("🦀♥", ferris);
	/// ```
	#[inline]
	pub unsafe fn from_utf8_unchecked(vec: ArrayVec<A>) -> ArrayString<A> {
		ArrayString { vec }
	}

	/// Returns an `ArrayString`'s backing [`ArrayVec`].
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 5]>::from("hello");
	/// let bytes = s.into_bytes();
	///
	/// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
	/// ```
	/// [`ArrayVec`]: https://docs.rs/tinyvec/0.3/tinyvec/struct.ArrayVec.html
	#[inline]
	pub fn into_bytes(self) -> ArrayVec<A> {
		self.vec
	}

	/// Extracts a string slice containing the entire `ArrayString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 3]>::from("foo");
	///
	/// assert_eq!("foo", s.as_str());
	/// ```
	#[inline]
	pub fn as_str(&self) -> &str {
		&*self
	}

	/// Extracts a mutable string slice containing the entire `ArrayString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 6]>::from("foobar");
	/// let s_mut_str = s.as_mut_str();
	///
	/// s_mut_str.make_ascii_uppercase();
	///
	/// assert_eq!("FOOBAR", s_mut_str);
	/// ```
	#[inline]
	pub fn as_mut_str(&mut self) -> &mut str {
		&mut *self
	}

	/// Returns a byte slice of this `ArrayString`'s contents.
	///
	/// The inverse of this method is [`from_utf8`].
	///
	/// [`from_utf8`]: #method.from_utf8
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 5]>::from("hello");
	///
	/// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
	/// ```
	#[inline]
	pub fn as_bytes(&self) -> &[u8] {
		&*self.vec
	}

	/// Returns a mutable reference to the contents of this `ArrayString`.
	///
	/// # Safety
	///
	/// This function is unsafe because it does not check that the bytes passed
	/// to it are valid UTF-8. If this constraint is violated, it may cause
	/// memory unsafety issues with future users of the `ArrayString`, as the
	/// rest of the standard library assumes that `ArrayString`s are valid
	/// UTF-8.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 5]>::from("hello");
	///
	/// unsafe {
	///     let vec = s.as_mut_vec();
	///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
	///
	///     vec.reverse();
	/// }
	/// assert_eq!(s, "olleh");
	/// ```
	#[inline]
	pub unsafe fn as_mut_vec(&mut self) -> &mut ArrayVec<A> {
		&mut self.vec
	}

	/// Returns this `ArrayString`'s capacity, in bytes.
	///
	/// This always returns a constant, the size of the backing array.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 16]>::new();
	///
	/// assert!(s.capacity() == 16);
	/// ```
	#[inline]
	pub fn capacity(&self) -> usize {
		self.vec.capacity()
	}

	/// Returns the length of this `ArrayString`, in bytes, not [`char`]s or
	/// graphemes. In other words, it may not be what a human considers the
	/// length of the string.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let plain_f = ArrayString::<[u8; 3]>::from("foo");
	/// assert_eq!(plain_f.len(), 3);
	///
	/// let fancy_f = ArrayString::<[u8; 4]>::from("ƒoo");
	/// assert_eq!(fancy_f.len(), 4);
	/// assert_eq!(fancy_f.chars().count(), 3);
	///
	/// let s = ArrayString::<[u8; 16]>::from("hello");
	/// assert_eq!(s.len(), 5);
	/// ```
	#[inline]
	pub fn len(&self) -> usize {
		self.vec.len()
	}

	/// Returns `true` if this `ArrayString` has a length of zero, and `false`
	/// otherwise.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 5]>::new();
	/// assert!(s.is_empty());
	///
	/// s.push('a');
	/// assert!(!s.is_empty());
	/// ```
	#[inline]
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Appends a given string slice onto the end of this `ArrayString`.
	///
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the
	/// backing array.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 6]>::from("foo");
	///
	/// s.push_str("bar");
	///
	/// assert_eq!("foobar", s);
	/// ```
	#[inline]
	pub fn push_str(&mut self, string: &str) {
		self.vec.extend_from_slice(string.as_bytes())
	}

	/// Appends the given [`char`] to the end of this `String`.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the
	/// backing array.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 6]>::from("abc");
	///
	/// s.push('1');
	/// s.push('2');
	/// s.push('3');
	///
	/// assert_eq!("abc123", s);
	/// ```
	#[inline]
	pub fn push(&mut self, ch: char) {
		match ch.len_utf8() {
			1 => self.vec.push(ch as u8),
			_ => self
				.vec
				.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
		}
	}

	/// Shortens this `ArrayString` to the specified length.
	///
	/// If `new_len` is greater than the string's current length, this has no
	/// effect.
	///
	/// Note that this method has no effect on the maximum capacity
	/// of the string
	///
	/// # Panics
	///
	/// Panics if `new_len` does not lie on a [`char`] boundary.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 5]>::from("hello");
	///
	/// s.truncate(2);
	///
	/// assert_eq!("he", s);
	/// ```
	#[inline]
	pub fn truncate(&mut self, new_len: usize) {
		if new_len <= self.len() {
			assert!(self.is_char_boundary(new_len));
			self.vec.truncate(new_len)
		}
	}

	/// Removes the last character from the string buffer and returns it.
	///
	/// Returns [`None`] if this `String` is empty.
	///
	/// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 3]>::from("foo");
	///
	/// assert_eq!(s.pop(), Some('o'));
	/// assert_eq!(s.pop(), Some('o'));
	/// assert_eq!(s.pop(), Some('f'));
	///
	/// assert_eq!(s.pop(), None);
	/// ```
	#[inline]
	pub fn pop(&mut self) -> Option<char> {
		let ch = self.chars().rev().next()?;
		let newlen = self.len() - ch.len_utf8();
		self.vec.set_len(newlen);
		Some(ch)
	}

	/// Removes a [`char`] from this `String` at a byte position and returns it.
	///
	/// This is an `O(n)` operation, as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than or equal to the `ArrayString`'s length,
	/// or if it does not lie on a [`char`] boundary.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 3]>::from("foo");
	///
	/// assert_eq!(s.remove(0), 'f');
	/// assert_eq!(s.remove(1), 'o');
	/// assert_eq!(s.remove(0), 'o');
	/// ```
	#[inline]
	pub fn remove(&mut self, idx: usize) -> char {
		let ch = match self[idx..].chars().next() {
			Some(ch) => ch,
			None => panic!("cannot remove a char from the end of a string"),
		};

		let next = idx + ch.len_utf8();
		let len = self.len();
		unsafe {
			ptr::copy(
				self.vec.as_ptr().add(next),
				self.vec.as_mut_ptr().add(idx),
				len - next,
			);
			self.vec.set_len(len - (next - idx));
		}
		ch
	}

	/// Retains only the characters specified by the predicate.
	///
	/// In other words, remove all characters `c` such that `f(c)` returns `false`.
	/// This method operates in place, visiting each character exactly once in the
	/// original order, and preserves the order of the retained characters.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 9]>::from("f_o_ob_ar");
	///
	/// s.retain(|c| c != '_');
	///
	/// assert_eq!(s, "foobar");
	/// ```
	///
	/// The exact order may be useful for tracking external state, like an index.
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 5]>::from("abcde");
	/// let keep = [false, true, true, false, true];
	/// let mut i = 0;
	/// s.retain(|_| (keep[i], i += 1).0);
	/// assert_eq!(s, "bce");
	/// ```
	#[inline]
	pub fn retain<F>(&mut self, mut f: F)
	where
		F: FnMut(char) -> bool,
	{
		let len = self.len();
		let mut del_bytes = 0;
		let mut idx = 0;

		while idx < len {
			let ch =
				unsafe { self.get_unchecked(idx..len).chars().next().unwrap() };
			let ch_len = ch.len_utf8();

			if !f(ch) {
				del_bytes += ch_len;
			} else if del_bytes > 0 {
				unsafe {
					ptr::copy(
						self.vec.as_ptr().add(idx),
						self.vec.as_mut_ptr().add(idx - del_bytes),
						ch_len,
					);
				}
			}

			// Point idx to the next char
			idx += ch_len;
		}

		if del_bytes > 0 {
			self.vec.set_len(len - del_bytes);
		}
	}

	/// Inserts a character into this `ArrayString` at a byte position.
	///
	/// This is an `O(n)` operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `ArrayString`'s length, or if it does not
	/// lie on a [`char`] boundary.
	///
	/// Panics if the new length would be longer than the capacity of the
	/// backing array.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 3]>::new();
	///
	/// s.insert(0, 'f');
	/// s.insert(1, 'o');
	/// s.insert(2, 'o');
	///
	/// assert_eq!("foo", s);
	/// ```
	#[inline]
	pub fn insert(&mut self, idx: usize, ch: char) {
		assert!(self.is_char_boundary(idx));
		let mut bits = [0; 4];
		let bits = ch.encode_utf8(&mut bits).as_bytes();

		unsafe {
			self.insert_bytes(idx, bits);
		}
	}

	/// Inserts a string slice into this `ArrayString` at a byte position.
	///
	/// This is an `O(n)` operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `String`'s length, or if it does not
	/// lie on a [`char`] boundary.
	///
	/// Panics if the new length would be longer than the capacity of the
	/// backing array.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 6]>::from("bar");
	///
	/// s.insert_str(0, "foo");
	///
	/// assert_eq!("foobar", s);
	/// ```
	#[inline]
	pub fn insert_str(&mut self, idx: usize, string: &str) {
		assert!(self.is_char_boundary(idx));

		unsafe {
			self.insert_bytes(idx, string.as_bytes());
		}
	}

	unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
		let len = self.len();
		let amt = bytes.len();

		assert!(
			len + amt <= self.capacity(),
			"ArrayString::insert_bytes: capacity overflow"
		);

		ptr::copy(
			self.vec.as_ptr().add(idx),
			self.vec.as_mut_ptr().add(idx + amt),
			len - idx,
		);
		ptr::copy(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
		self.vec.set_len(len + amt);
	}

	/// Truncates this `ArrayString`, removing all contents.
	///
	/// While this means the `ArrayString` will have a length of zero, it does
	/// not modify its capacity.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 3]>::from("foo");
	///
	/// s.clear();
	///
	/// assert!(s.is_empty());
	/// assert_eq!(0, s.len());
	/// assert_eq!(3, s.capacity());
	/// ```
	#[inline]
	pub fn clear(&mut self) {
		self.vec.clear()
	}

	/// Creates a draining iterator that removes the specified range in the `String`
	/// and yields the removed `chars`.
	///
	/// Note: The element range is removed even if the iterator is not
	/// consumed until the end.
	///
	/// # Panics
	///
	/// Panics if the starting point or end point do not lie on a [`char`]
	/// boundary, or if they're out of bounds.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut s = ArrayString::<[u8; 23]>::from("α is alpha, β is beta");
	/// let beta_offset = s.find('β').unwrap_or(s.len());
	///
	/// // Remove the range up until the β from the string
	/// let t: ArrayString<[u8; 23]> = s.drain(..beta_offset).collect();
	/// assert_eq!(t, "α is alpha, ");
	/// assert_eq!(s, "β is beta");
	///
	/// // A full range clears the string
	/// s.drain(..);
	/// assert_eq!(s, "");
	/// ```
	pub fn drain<R>(&mut self, range: R) -> Drain<'_, A>
	where
		R: RangeBounds<usize>,
	{
		use Bound::*;

		let len = self.len();
		let start = match range.start_bound() {
			Included(&n) => n,
			Excluded(&n) => n + 1,
			Unbounded => 0,
		};
		let end = match range.end_bound() {
			Included(&n) => n + 1,
			Excluded(&n) => n,
			Unbounded => len,
		};

		// Take out two simultaneous borrows. The &mut String won't be accessed
		// until iteration is over, in Drop.
		let self_ptr = self as *mut _;
		// slicing does the appropriate bounds checks
		let chars_iter = self[start..end].chars();

		Drain {
			start,
			end,
			iter: chars_iter,
			string: self_ptr,
		}
	}
}

impl<A: Array<Item = u8> + Default> ArrayString<A> {
	/// Splits the string into two at the given index.
	///
	/// Returns a new `ArrayString`. `self` contains bytes `[0, at)`, and
	/// the returned `ArrayString` contains bytes `[at, len)`. `at` must be on
	/// the boundary of a UTF-8 code point.
	///
	/// Both `self` and the returned `ArrayString` will have the same capacity
	/// as `self` did before this was called.
	///
	/// # Panics
	///
	/// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
	/// code point of the string.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let mut hello = ArrayString::<[u8; 13]>::from("Hello, World!");
	/// let world = hello.split_off(7);
	/// assert_eq!(hello, "Hello, ");
	/// assert_eq!(world, "World!");
	/// ```
	#[inline]
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> ArrayString<A> {
		assert!(self.is_char_boundary(at));
		let other = self.vec.split_off(at);
		unsafe { ArrayString::from_utf8_unchecked(other) }
	}
}

impl ArrayString<[u8; 4]> {
	/// Creates an `ArrayString` from a `char` infallibly.
	///
	/// Without const generics, this method is limited to `ArrayString`s with
	/// backing arrays of size 4 only.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 4]>::from_char_infallible('c');
	/// assert_eq!(s, "c");
	/// ```
	pub fn from_char_infallible(c: char) -> Self {
		let mut arr = [0u8; 4];
		let len = c.encode_utf8(&mut arr).len();
		unsafe { Self::from_utf8_unchecked(ArrayVec::from_array_len(arr, len)) }
	}
}

impl<A: Array<Item = u8>> Deref for ArrayString<A> {
	type Target = str;

	fn deref(&self) -> &str {
		unsafe { str::from_utf8_unchecked(&*self.vec) }
	}
}

impl<A: Array<Item = u8>> DerefMut for ArrayString<A> {
	fn deref_mut(&mut self) -> &mut str {
		unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
	}
}

impl<A: Array<Item = u8>> fmt::Display for ArrayString<A> {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(&**self, f)
	}
}

impl<A: Array<Item = u8>> fmt::Debug for ArrayString<A> {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(&**self, f)
	}
}

impl<A: Array<Item = u8>> Hash for ArrayString<A> {
	#[inline]
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		(**self).hash(hasher)
	}
}

impl<A: Array<Item = u8> + Clone> Clone for ArrayString<A> {
	fn clone(&self) -> Self {
		ArrayString {
			vec: self.vec.clone(),
		}
	}

	fn clone_from(&mut self, source: &Self) {
		self.vec.clone_from(&source.vec);
	}
}

impl<A: Array<Item = u8> + Default, A2: Array<Item = u8>>
	FromIterator<ArrayString<A2>> for ArrayString<A>
{
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn from_iter<I: IntoIterator<Item = ArrayString<A2>>>(iter: I) -> Self {
		let mut buf = Self::new();
		buf.extend(iter);
		buf
	}
}

macro_rules! impl_from_iterator {
	($(#[$meta:meta])* $ty:ty) => {
		$(#[$meta])*
		#[allow(unused_lifetimes)]
		impl<'a, A: Array<Item = u8> + Default> FromIterator<$ty>
			for ArrayString<A>
		{
			/// # Panics
			///
			/// Panics if the length would be longer than the capacity of the
			/// backing array.
			fn from_iter<I: IntoIterator<Item = $ty>>(iter: I) -> Self {
				let mut buf = Self::new();
				buf.extend(iter);
				buf
			}
		}
	};
}

impl_from_iterator!(
#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")] Cow<'a, str>);
impl_from_iterator!(
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
	#[cfg(feature = "alloc")]
	String
);
impl_from_iterator!(&'a str);
impl_from_iterator!(&'a char);
impl_from_iterator!(char);

impl<A: Array<Item = u8>> Extend<char> for ArrayString<A> {
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
		let iterator = iter.into_iter();
		iterator.for_each(move |c| self.push(c));
	}
}

impl<'a, A: Array<Item = u8>> Extend<&'a char> for ArrayString<A> {
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
		self.extend(iter.into_iter().copied());
	}
}

impl<'a, A: Array<Item = u8>> Extend<&'a str> for ArrayString<A> {
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(s));
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<A: Array<Item = u8>> Extend<String> for ArrayString<A> {
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = String>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

impl<A: Array<Item = u8>, A2: Array<Item = u8>> Extend<ArrayString<A2>>
	for ArrayString<A>
{
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = ArrayString<A2>>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, A: Array<Item = u8>> Extend<Cow<'a, str>> for ArrayString<A> {
	/// # Panics
	///
	/// Panics if the new length would be longer than the capacity of the backing
	/// array.
	fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

macro_rules! impl_eq {
	($(#[$meta:meta])* $lhs:ty, $rhs: ty) => {
		$(#[$meta])*
		#[allow(unused_lifetimes)]
		impl<'a, 'b, A: Array<Item = u8>> PartialEq<$rhs> for $lhs {
			#[inline]
			fn eq(&self, other: &$rhs) -> bool {
				PartialEq::eq(&self[..], &other[..])
			}
			#[inline]
			fn ne(&self, other: &$rhs) -> bool {
				PartialEq::ne(&self[..], &other[..])
			}
		}

		$(#[$meta])*
		#[allow(unused_lifetimes)]
		impl<'a, 'b, A: Array<Item = u8>> PartialEq<$lhs> for $rhs {
			#[inline]
			fn eq(&self, other: &$lhs) -> bool {
				PartialEq::eq(&self[..], &other[..])
			}
			#[inline]
			fn ne(&self, other: &$lhs) -> bool {
				PartialEq::ne(&self[..], &other[..])
			}
		}
	};
}

impl_eq! { ArrayString<A>, str }
impl_eq! { ArrayString<A>, &'a str }
impl_eq! {
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
	#[cfg(feature = "alloc")]
	ArrayString<A>, Cow<'a, str>
}
impl_eq! {
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
	#[cfg(feature = "alloc")]
	ArrayString<A>, String
}

impl<A1, A2> PartialEq<ArrayString<A1>> for ArrayString<A2>
where
	A1: Array<Item = u8>,
	A2: Array<Item = u8>,
{
	#[inline]
	fn eq(&self, other: &ArrayString<A1>) -> bool {
		PartialEq::eq(&self[..], &other[..])
	}
	#[inline]
	fn ne(&self, other: &ArrayString<A1>) -> bool {
		PartialEq::ne(&self[..], &other[..])
	}
}

/// Implements the `+` operator for concatenating two strings.
///
/// # Panics
///
/// Panics if the new length would be longer than the capacity of the backing
/// array.
///
/// # Examples
///
/// ```
/// # use tinyvec_string::ArrayString;
/// use std::convert::TryFrom;
/// let a = ArrayString::<[u8; 13]>::from("Hello, ");
/// let b = "World!";
/// let c = a + b;
/// assert_eq!(c, "Hello, World!");
/// ```
impl<A: Array<Item = u8> + Default> Add<&str> for ArrayString<A> {
	type Output = ArrayString<A>;

	#[inline]
	fn add(mut self, other: &str) -> Self {
		self.push_str(other);
		self
	}
}

/// Implements the `+=` operator for appending to a `String`.
///
/// This has the same behavior as the [`push_str`] method.
///
/// # Panics
///
/// Panics if the new length would be longer than the capacity of the backing
/// array.
///
/// # Examples
///
/// ```
/// # use tinyvec_string::ArrayString;
/// use std::convert::TryFrom;
/// let mut a = ArrayString::<[u8; 13]>::from("Hello, ");
/// let b = "World!";
/// a += b;
/// assert_eq!(a, "Hello, World!");
/// ```
///
/// [`push_str`]: struct.ArrayString.html#method.push_str
impl<A: Array<Item = u8>> AddAssign<&str> for ArrayString<A> {
	#[inline]
	fn add_assign(&mut self, other: &str) {
		self.push_str(other);
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::Range<usize>> for ArrayString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::Range<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::RangeTo<usize>> for ArrayString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeTo<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::RangeFrom<usize>> for ArrayString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeFrom<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::RangeFull> for ArrayString<A> {
	type Output = str;

	#[inline]
	fn index(&self, _index: ops::RangeFull) -> &str {
		unsafe { str::from_utf8_unchecked(&self.vec) }
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::RangeInclusive<usize>>
	for ArrayString<A>
{
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
		Index::index(&**self, index)
	}
}

impl<A: Array<Item = u8>> ops::Index<ops::RangeToInclusive<usize>>
	for ArrayString<A>
{
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
		Index::index(&**self, index)
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::Range<usize>> for ArrayString<A> {
	#[inline]
	fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::RangeTo<usize>>
	for ArrayString<A>
{
	#[inline]
	fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::RangeFrom<usize>>
	for ArrayString<A>
{
	#[inline]
	fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::RangeFull> for ArrayString<A> {
	#[inline]
	fn index_mut(&mut self, _index: ops::RangeFull) -> &mut str {
		unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::RangeInclusive<usize>>
	for ArrayString<A>
{
	#[inline]
	fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
		IndexMut::index_mut(&mut **self, index)
	}
}

impl<A: Array<Item = u8>> ops::IndexMut<ops::RangeToInclusive<usize>>
	for ArrayString<A>
{
	#[inline]
	fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
		IndexMut::index_mut(&mut **self, index)
	}
}

impl<A: Array<Item = u8>> AsRef<str> for ArrayString<A> {
	#[inline]
	fn as_ref(&self) -> &str {
		&*self
	}
}

impl<A: Array<Item = u8>> AsMut<str> for ArrayString<A> {
	#[inline]
	fn as_mut(&mut self) -> &mut str {
		&mut *self
	}
}

impl<A: Array<Item = u8>> AsRef<[u8]> for ArrayString<A> {
	#[inline]
	fn as_ref(&self) -> &[u8] {
		self.as_bytes()
	}
}

/// An error was caused converting another string type into an [`ArrayString`].
///
/// This type contains the amount by which the capacity was overflown, and the
/// input string (when possible).
///
/// # Examples
/// ```
/// # use tinyvec_string::arraystring::{ArrayString, CapacityOverflowError};
/// use std::convert::TryFrom;
/// let result = ArrayString::<[u8; 3]>::try_from("foobar");
///
/// assert!(result.is_err());
/// let err: CapacityOverflowError<&str> = result.unwrap_err();
///
/// assert_eq!(err.overflow_amount(), 3);
/// assert_eq!(err.into_inner(), "foobar");
/// ```
///
/// [`ArrayString`]: struct.ArrayString.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CapacityOverflowError<S> {
	overflow_amount: usize,
	inner: S,
}

impl<S> CapacityOverflowError<S> {
	/// Get the amount by which the capacity was overflown, i.e. the amount of
	/// extra capacity that would've been needed to store the string.
	pub fn overflow_amount(&self) -> usize {
		self.overflow_amount
	}

	/// Retrieve the input string.
	///
	/// # Examples
	///
	/// This could be used to retrieve a `String` that failed to convert:
	/// ```
	/// # use tinyvec_string::arraystring::{ArrayString, CapacityOverflowError};
	/// use std::convert::TryFrom;
	/// let heap_string = String::from("a very long string");
	/// let result = ArrayString::<[u8; 5]>::try_from(heap_string);
	///
	/// assert!(result.is_err());
	/// let err: CapacityOverflowError<String> = result.unwrap_err();
	/// let return_of_the_heap_string = err.into_inner();
	///
	/// assert_eq!(return_of_the_heap_string, String::from("a very long string"));
	/// ```
	pub fn into_inner(self) -> S {
		self.inner
	}
}

impl<S: fmt::Display> fmt::Display for CapacityOverflowError<S> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			r#"Failed to convert "{}" to an ArrayString: capacity overflowed by {} bytes"#,
			self.inner, self.overflow_amount
		)
	}
}

impl<'a, A: Array<Item = u8> + Default> TryFrom<&'a str> for ArrayString<A> {
	type Error = CapacityOverflowError<&'a str>;

	fn try_from(s: &'a str) -> Result<Self, Self::Error> {
		let mut arr = A::default();
		let slice = arr.as_slice_mut();
		if s.len() <= slice.len() {
			slice[..s.len()].copy_from_slice(s.as_bytes());
			unsafe {
				Ok(Self::from_utf8_unchecked(ArrayVec::from_array_len(
					arr,
					s.len(),
				)))
			}
		} else {
			Err(CapacityOverflowError {
				overflow_amount: s.len() - slice.len(),
				inner: s,
			})
		}
	}
}

impl<'a, A: Array<Item = u8> + Default> TryFrom<&'a mut str>
	for ArrayString<A>
{
	type Error = CapacityOverflowError<&'a mut str>;

	fn try_from(s: &'a mut str) -> Result<Self, Self::Error> {
		match Self::try_from(&*s) {
			Ok(s) => Ok(s),
			Err(e) => Err(CapacityOverflowError {
				overflow_amount: e.overflow_amount,
				inner: s,
			}),
		}
	}
}

impl<'c, A: Array<Item = u8> + Default> TryFrom<&'c char> for ArrayString<A> {
	type Error = CapacityOverflowError<&'c char>;

	fn try_from(c: &'c char) -> Result<Self, Self::Error> {
		let mut buf = [0u8; 4];
		let s = c.encode_utf8(&mut buf);
		Self::try_from(&*s).map_err(|e| CapacityOverflowError {
			overflow_amount: e.overflow_amount,
			inner: c,
		})
	}
}

impl<A: Array<Item = u8> + Default> TryFrom<char> for ArrayString<A> {
	type Error = CapacityOverflowError<char>;

	fn try_from(c: char) -> Result<Self, Self::Error> {
		let mut buf = [0u8; 4];
		let s = c.encode_utf8(&mut buf);
		Self::try_from(&*s).map_err(|e| CapacityOverflowError {
			overflow_amount: e.overflow_amount,
			inner: c,
		})
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, A: Array<Item = u8> + Default> TryFrom<&'a String> for ArrayString<A> {
	type Error = CapacityOverflowError<&'a String>;

	fn try_from(s: &'a String) -> Result<Self, Self::Error> {
		Self::try_from(s.as_str()).map_err(|e| CapacityOverflowError {
			overflow_amount: e.overflow_amount,
			inner: s,
		})
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<A: Array<Item = u8> + Default> TryFrom<String> for ArrayString<A> {
	type Error = CapacityOverflowError<String>;

	fn try_from(s: String) -> Result<Self, Self::Error> {
		match Self::try_from(&*s) {
			Ok(s) => Ok(s),
			Err(e) => Err(CapacityOverflowError {
				overflow_amount: e.overflow_amount,
				inner: s,
			}),
		}
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, A: Array<Item = u8> + Default> TryFrom<Cow<'a, str>>
	for ArrayString<A>
{
	type Error = CapacityOverflowError<Cow<'a, str>>;

	fn try_from(s: Cow<'a, str>) -> Result<Self, Self::Error> {
		match Self::try_from(&*s) {
			Ok(s) => Ok(s),
			Err(e) => Err(CapacityOverflowError {
				overflow_amount: e.overflow_amount,
				inner: s,
			}),
		}
	}
}

impl<A: Array<Item = u8> + Default> FromStr for ArrayString<A> {
	/// Because of lifetime restrictions, the error type can't return the
	/// provided string like the `TryFrom` implementations do.
	type Err = CapacityOverflowError<()>;
	#[inline]
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Self::try_from(s).map_err(|e| CapacityOverflowError {
			overflow_amount: e.overflow_amount,
			inner: (),
		})
	}
}

impl<A: Array<Item = u8>> fmt::Write for ArrayString<A> {
	#[inline]
	fn write_str(&mut self, s: &str) -> fmt::Result {
		self.push_str(s);
		Ok(())
	}

	#[inline]
	fn write_char(&mut self, c: char) -> fmt::Result {
		self.push(c);
		Ok(())
	}
}

/// A possible error value when converting an [`ArrayString`] from a UTF-8 byte
/// vector.
///
/// This type is the error type for the [`from_utf8`] method on `ArrayString`.
/// The [`into_bytes`] method will give back the byte vector that was used in
/// the conversion attempt.
///
/// [`from_utf8`]: struct.ArrayString.html#method.from_utf8
/// [`ArrayString`]: struct.ArrayString.html
/// [`into_bytes`]: struct.FromUtf8Error.html#method.into_bytes
///
/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
/// an analogue to `FromUtf8Error`, and you can get one from a `FromUtf8Error`
/// through the [`utf8_error`] method.
///
/// [`Utf8Error`]: https://doc.rust-lang.org/std/str/struct.Utf8Error.html
/// [`std::str`]: https://doc.rust-lang.org/std/str/index.html
/// [`u8`]: https://doc.rust-lang.org/std/primitive.u8.html
/// [`&str`]: https://doc.rust-lang.org/std/primitive.str.html
/// [`utf8_error`]: struct.FromUtf8Error.html#method.utf8_error
///
/// # Examples
///
/// ```
/// # use tinyvec_string::ArrayString;
/// use tinyvec::{array_vec, ArrayVec};
/// // some invalid bytes, in a vector
/// let bytes: ArrayVec<[u8; 2]> = array_vec![0, 159];
///
/// let value = ArrayString::from_utf8(bytes);
///
/// assert_eq!(Err(array_vec![0, 159]), value.map_err(|e| e.into_bytes()));
/// ```
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FromUtf8Error<A: Array<Item = u8>> {
	vec: ArrayVec<A>,
	error: Utf8Error,
}

impl<A: Array<Item = u8>> FromUtf8Error<A> {
	/// Returns a slice of [`u8`]s bytes that were attempted to convert to an
	/// `ArrayString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	/// // some invalid bytes, in a vector
	/// let bytes: ArrayVec<[u8; 2]> = array_vec![0, 159];
	///
	/// let value = ArrayString::from_utf8(bytes);
	///
	/// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
	/// ```
	pub fn as_bytes(&self) -> &[u8] {
		&self.vec[..]
	}

	/// Returns the bytes that were attempted to convert to a `String`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	/// // some invalid bytes, in a vector
	/// let bytes: ArrayVec<[u8; 2]> = array_vec![0, 159];
	///
	/// let value = ArrayString::from_utf8(bytes);
	///
	/// assert_eq!(array_vec![0, 159], value.unwrap_err().into_bytes());
	/// ```
	pub fn into_bytes(self) -> ArrayVec<A> {
		self.vec
	}

	/// Fetch a `Utf8Error` to get more details about the conversion failure.
	///
	/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
	/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
	/// an analogue to `FromUtf8Error`. See its documentation for more details
	/// on using it.
	///
	/// [`Utf8Error`]: https://doc.rust-lang.org/std/str/struct.Utf8Error.html
	/// [`std::str`]: https://doc.rust-lang.org/std/str/index.html
	/// [`u8`]: https://doc.rust-lang.org/std/primitive.u8.html
	/// [`&str`]: https://doc.rust-lang.org/std/primitive.str.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// use tinyvec::{array_vec, ArrayVec};
	/// // some invalid bytes, in a vector
	/// let bytes: ArrayVec<[u8; 2]> = array_vec![0, 159];
	///
	/// let error = ArrayString::from_utf8(bytes).unwrap_err().utf8_error();
	///
	/// // the first byte is invalid here
	/// assert_eq!(1, error.valid_up_to());
	/// ```
	pub fn utf8_error(&self) -> Utf8Error {
		self.error
	}
}

impl<A: Array<Item = u8>> fmt::Debug for FromUtf8Error<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("FromUtf8Error")
			.field("vec", &self.vec)
			.field("error", &self.error)
			.finish()
	}
}

impl<A: Array<Item = u8>> fmt::Display for FromUtf8Error<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(&self.error, f)
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "std")))]
#[cfg(feature = "std")]
impl<A: Array<Item = u8>> std::error::Error for FromUtf8Error<A> {}

/// A draining iterator for [`ArrayString`].
///
/// This struct is created by the [`drain`] method on [`ArrayString`]. See its
/// documentation for more.
///
/// [`drain`]: struct.ArrayString.html#method.drain
/// [`ArrayString`]: struct.ArrayString.html
pub struct Drain<'a, A: Array<Item = u8>> {
	/// Will be used as &'a mut ArrayString in the destructor
	string: *mut ArrayString<A>,
	/// Start of part to remove
	start: usize,
	/// End of part to remove
	end: usize,
	/// Current remaining range to remove
	iter: Chars<'a>,
}

impl<A: Array<Item = u8>> fmt::Debug for Drain<'_, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.pad("Drain { .. }")
	}
}

unsafe impl<A: Array<Item = u8>> Send for Drain<'_, A> {}
unsafe impl<A: Array<Item = u8>> Sync for Drain<'_, A> {}

impl<A: Array<Item = u8>> Drop for Drain<'_, A> {
	fn drop(&mut self) {
		unsafe {
			// Use Vec::drain. "Reaffirm" the bounds checks to avoid
			// panic code being inserted again.
			let self_vec = (*self.string).as_mut_vec();
			if self.start <= self.end && self.end <= self_vec.len() {
				self_vec.drain(self.start..self.end);
			}
		}
	}
}

impl<A: Array<Item = u8>> Iterator for Drain<'_, A> {
	type Item = char;

	#[inline]
	fn next(&mut self) -> Option<char> {
		self.iter.next()
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}

	#[inline]
	fn last(mut self) -> Option<char> {
		self.next_back()
	}
}

impl<A: Array<Item = u8>> DoubleEndedIterator for Drain<'_, A> {
	#[inline]
	fn next_back(&mut self) -> Option<char> {
		self.iter.next_back()
	}
}

impl<A: Array<Item = u8>> FusedIterator for Drain<'_, A> {}
