//! Inline/Heap strings.
//!
//! Requires the `alloc` cargo feature to be enabled.
use crate::{arraystring::ArrayString, bytearray::ByteArray, tinyvec::TinyVec};

use core::{
	convert::Infallible,
	fmt,
	hash::{Hash, Hasher},
	iter::{DoubleEndedIterator, FromIterator, FusedIterator},
	ops::{
		self, Add, AddAssign, Bound, Deref, DerefMut, Index, IndexMut,
		RangeBounds,
	},
	str::{self, Chars, FromStr, Utf8Error},
};

use alloc::{borrow::Cow, string::String};

use tinyvec_macros::impl_mirrored;

/// A UTF-8 encoded, fixed-capacity string.
///
/// A `TinyString` is similar to [`String`], but may be stored inline as an
/// [`ArrayString`]. This means it has similar characteristics to `TinyVec`:
/// * A `TinyString` has a dynamic length; characters can be added and
///   removed.
/// * An inline `TinyString` has a fixed capacity (in bytes), the size of the
///   backing array.
/// * A heap `TinyString` has a dynamic capacity.
/// * If characters are added to an inline `TinyString` such that its new length
///   would overflow the capacity of the backing array, it is moved to the heap.
///
/// Like `String`, the contents of an `TinyString` must be valid UTF-8 at all
/// times.
///
/// `TinyString` is intended to replicate the API of `String` as much as
/// possible.
///
/// Requires the `alloc` cargo feature to be enabled.
///
/// [`String`]: https://doc.rust-lang.org/std/string/struct.String.html
/// [`TinyVec`]: ../tinyvec/enum.TinyVec.html
/// [`ArrayString`]: ../arraystring/struct.ArrayString.html
#[derive(Eq, PartialOrd, Ord)]
#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
pub enum TinyString<A: ByteArray> {
	Inline(ArrayString<A>),
	Heap(String),
}

/// Creates an empty inline `TinyString`.
impl<A: ByteArray> Default for TinyString<A> {
	fn default() -> Self {
		TinyString::Inline(ArrayString::default())
	}
}

impl<A: ByteArray> TinyString<A> {
	/// Creates a new empty inline `TinyString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// // create an `TinyString` with 16 bytes of capacity
	/// let s = TinyString::<[u8; 16]>::new();
	/// ```
	#[inline]
	pub fn new() -> TinyString<A> {
		TinyString::default()
	}

	/// Creates a new empty `TinyString` with the provided capacity.
	///
	/// If the provided capacity is less than or equal to the inline capacity,
	/// the returned `TinyString` will be inline, otherwise it will be on the
	/// heap.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let s = TinyString::<[u8; 8]>::with_capacity(8);
	/// assert!(s.is_inline());
	/// assert_eq!(s.capacity(), 8);
	///
	/// let s = TinyString::<[u8; 8]>::with_capacity(16);
	/// assert!(s.is_heap());
	/// assert!(s.capacity() >= 16);
	/// ```
	pub fn with_capacity(capacity: usize) -> TinyString<A> {
		if capacity <= A::CAPACITY {
			TinyString::Inline(ArrayString::default())
		} else {
			TinyString::Heap(String::with_capacity(capacity))
		}
	}

	/// Converts a vector of bytes to an `TinyString`.
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
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	/// // some bytes, in a vector
	/// let ferris: TinyVec<[u8; 7]> = tiny_vec![240, 159, 166, 128, 226, 153, 165];
	///
	/// // We know these bytes are valid UTF-8, so we'll use `unwrap()`.
	/// let ferris = TinyString::from_utf8(ferris).unwrap();
	///
	/// assert_eq!("🦀♥", ferris);
	/// ```
	///
	/// Incorrect bytes:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	///
	/// // some invalid bytes, in a vector
	/// let ferris: TinyVec<[u8; 7]> = tiny_vec![0, 159, 166, 128, 226, 153, 165];
	///
	/// assert!(TinyString::from_utf8(ferris).is_err());
	/// ```
	///
	/// See the docs for [`FromUtf8Error`] for more details on what you can do
	/// with this error.
	///
	/// [`into_bytes`]: #method.into_bytes
	/// [`FromUtf8Error`]: struct.FromUtf8Error.html
	#[inline]
	pub fn from_utf8(
		vec: TinyVec<A>,
	) -> Result<TinyString<A>, FromUtf8Error<A>> {
		match vec {
			TinyVec::Inline(vec) => match ArrayString::from_utf8(vec) {
				Ok(s) => Ok(TinyString::Inline(s)),
				Err(e) => Err(FromUtf8Error {
					error: e.error,
					vec: TinyVec::Inline(e.vec),
				}),
			},
			TinyVec::Heap(vec) => match String::from_utf8(vec) {
				Ok(s) => Ok(TinyString::Heap(s)),
				Err(e) => Err(FromUtf8Error {
					error: e.utf8_error(),
					vec: TinyVec::Heap(e.into_bytes()),
				}),
			},
		}
	}

	/// Converts a vector of bytes to an `TinyString` without checking that
	/// the string contains valid UTF-8.
	///
	/// See the safe version, [`from_utf8`], for more details.
	///
	/// [`from_utf8`]: enum.TinyString.html#method.from_utf8
	///
	/// # Safety
	///
	/// This function is unsafe because it does not check that the bytes passed
	/// to it are valid UTF-8. If this constraint is violated, it may cause
	/// memory unsafety issues with future users of the `TinyString`, as the
	/// rest of this library and the standard library assumes that `str`s are
	/// valid UTF-8.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	/// // some bytes, in a vector
	/// let ferris: TinyVec<[u8; 7]> = tiny_vec![240, 159, 166, 128, 226, 153, 165];
	///
	/// let ferris = unsafe {
	/// 	// we know these bytes are valid UTF-8, so this is sound.
	///		TinyString::from_utf8_unchecked(ferris)
	/// };
	///
	/// assert_eq!("🦀♥", ferris);
	/// ```
	#[inline]
	pub unsafe fn from_utf8_unchecked(vec: TinyVec<A>) -> TinyString<A> {
		match vec {
			TinyVec::Inline(vec) => {
				TinyString::Inline(ArrayString::from_utf8_unchecked(vec))
			}
			TinyVec::Heap(vec) => {
				TinyString::Heap(String::from_utf8_unchecked(vec))
			}
		}
	}

	/// Returns a `TinyString`'s backing bytes as a [`TinyVec`].
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let s = TinyString::<[u8; 5]>::from("hello");
	/// let bytes = s.into_bytes();
	///
	/// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
	/// ```
	/// [`TinyVec`]: ../tinyvec/enum.TinyVec.html
	#[inline]
	pub fn into_bytes(self) -> TinyVec<A> {
		match self {
			TinyString::Inline(s) => TinyVec::Inline(s.into_bytes()),
			TinyString::Heap(s) => TinyVec::Heap(s.into_bytes()),
		}
	}

	/// Extracts a string slice containing the entire `TinyString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let s = TinyString::<[u8; 3]>::from("foo");
	///
	/// assert_eq!("foo", s.as_str());
	/// ```
	#[inline]
	pub fn as_str(&self) -> &str {
		&*self
	}

	/// Extracts a mutable string slice containing the entire `TinyString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 6]>::from("foobar");
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

	impl_mirrored! {
		type Mirror = TinyString;

		/// Returns a byte slice of this `TinyString`'s contents.
		///
		/// The inverse of this method is [`from_utf8`].
		///
		/// [`from_utf8`]: #method.from_utf8
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let s = TinyString::<[u8; 5]>::from("hello");
		///
		/// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
		/// ```
		#[inline]
		pub fn as_bytes(self: &Self) -> &[u8];
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Returns this `TinyString`'s capacity, in bytes.
		///
		/// This always returns a constant, the size of the backing array.
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// let s = TinyString::<[u8; 16]>::new();
		///
		/// assert!(s.capacity() == 16);
		/// ```
		#[inline]
		pub fn capacity(self: &Self) -> usize;
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Returns the length of this `TinyString`, in bytes, not [`char`]s or
		/// graphemes. In other words, it may not be what a human considers the
		/// length of the string.
		///
		/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let plain_f = TinyString::<[u8; 3]>::from("foo");
		/// assert_eq!(plain_f.len(), 3);
		///
		/// let fancy_f = TinyString::<[u8; 4]>::from("ƒoo");
		/// assert_eq!(fancy_f.len(), 4);
		/// assert_eq!(fancy_f.chars().count(), 3);
		///
		/// let s = TinyString::<[u8; 16]>::from("hello");
		/// assert_eq!(s.len(), 5);
		/// ```
		#[inline]
		pub fn len(self: &Self) -> usize;
	}

	/// Returns `true` if this `TinyString` has a length of zero, and `false`
	/// otherwise.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::new();
	/// assert!(s.is_empty());
	///
	/// s.push('a');
	/// assert!(!s.is_empty());
	/// ```
	#[inline]
	pub fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Returns `true` if this `TinyString` is on the heap, and `false`
	/// otherwise.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::new();
	/// s.push_str("hello world");
	/// assert!(s.is_heap());
	/// ```
	#[inline]
	pub fn is_heap(&self) -> bool {
		match self {
			TinyString::Inline(_) => false,
			TinyString::Heap(_) => true,
		}
	}

	/// Returns `true` if this `TinyString` is inline, and `false`
	/// otherwise.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 16]>::new();
	/// s.push_str("hello world");
	/// assert!(s.is_inline());
	/// ```
	#[inline]
	pub fn is_inline(&self) -> bool {
		match self {
			TinyString::Inline(_) => true,
			TinyString::Heap(_) => false,
		}
	}

	/// Ensures that this `TinyString`'s capacity is at least `additional` bytes
	/// larger than its length.
	///
	/// If this `TinyString` is already in the heap, the capacity may be
	/// increased by more than `additional` bytes if it chooses, to prevent
	/// frequent reallocations.
	///
	/// If you do not want this "at least" behavior, see the [`reserve_exact`]
	/// method.
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows [`usize`].
	///
	/// [`reserve_exact`]: #method.reserve_exact
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::new();
	///
	/// s.reserve(10);
	///
	/// assert!(s.capacity() >= 10);
	/// ```
	///
	/// This might not actually increase the capacity:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 10]>::new();
	/// s.push('a');
	/// s.push('b');
	///
	/// // s now has a length of 2 and a capacity of 10
	/// assert_eq!(2, s.len());
	/// assert_eq!(10, s.capacity());
	///
	/// // Since we already have an extra 8 capacity, calling this...
	/// s.reserve(8);
	///
	/// // ... doesn't actually increase.
	/// assert_eq!(10, s.capacity());
	/// ```
	#[inline]
	pub fn reserve(&mut self, additional: usize) {
		match self {
			TinyString::Inline(s) => {
				if s.len() + additional > s.capacity() {
					let mut heap = String::with_capacity(s.len() + additional);
					heap.push_str(s.as_str());
					*self = TinyString::Heap(heap);
				}
			}
			TinyString::Heap(s) => s.reserve(additional),
		}
	}

	/// Ensures that this `TinyString`'s capacity is `additional` bytes
	/// larger than its length.
	///
	/// Consider using the [`reserve`] method unless you absolutely know
	/// better than the allocator.
	///
	/// This has no effect if the `TinyString` is inline and the new capacity
	/// would be less than or equal to the capacity of the backing array, even
	/// if it is not exact.
	///
	/// [`reserve`]: #method.reserve
	///
	/// # Panics
	///
	/// Panics if the new capacity overflows `usize`.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::new();
	///
	/// s.reserve_exact(10);
	///
	/// assert!(s.capacity() >= 10);
	///
	/// s.reserve_exact(20);
	///
	/// assert!(s.capacity() >= 20);
	/// ```
	///
	/// This might not actually increase the capacity:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 10]>::new();
	/// s.push('a');
	/// s.push('b');
	///
	/// // s now has a length of 2 and a capacity of 10
	/// assert_eq!(2, s.len());
	/// assert_eq!(10, s.capacity());
	///
	/// // Since we already have an extra 8 capacity, calling this...
	/// s.reserve_exact(8);
	///
	/// // ... doesn't actually increase.
	/// assert_eq!(10, s.capacity());
	/// ```
	#[inline]
	pub fn reserve_exact(&mut self, additional: usize) {
		match self {
			TinyString::Inline(s) => {
				if s.len() + additional > s.capacity() {
					let mut heap = String::with_capacity(s.len() + additional);
					heap.push_str(s.as_str());
					*self = TinyString::Heap(heap);
				}
			}
			TinyString::Heap(s) => s.reserve_exact(additional),
		}
	}

	/// Tries to reserve capacity for at least `additional` more bytes to be
	/// inserted in the given `TinyString`. The collection may reserve more
	/// space to avoid frequent reallocations. After calling `reserve`,
	/// capacity will be greater than or equal to `self.len() + additional`.
	/// Does nothing if capacity is already sufficient.
	///
	/// # Errors
	///
	/// If the capacity overflows, or the allocator reports a failure, then an error
	/// is returned.
	///
	/// # Examples
	///
	/// ```
	/// # const N: usize = 1;
	/// # use tinyvec_string::TinyString;
	/// use std::collections::TryReserveError;
	///
	/// fn process_data(data: &str) -> Result<TinyString<[u8; N]>, TryReserveError> {
	///     let mut output = TinyString::new();
	///
	///     // Pre-reserve the memory, exiting if we can't
	///     output.try_reserve(data.len())?;
	///
	///     // Now we know this can't OOM in the middle of our complex work
	///     output.push_str(data);
	///
	///     Ok(output)
	/// }
	/// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
	/// ```
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "rustc_1_57")))]
	#[cfg(feature = "rustc_1_57")]
	pub fn try_reserve(
		&mut self,
		additional: usize,
	) -> Result<(), alloc::collections::TryReserveError> {
		match self {
			TinyString::Inline(s) => match s.len().checked_add(additional) {
				Some(new_cap) if new_cap > s.capacity() => {
					let mut heap = String::new();
					heap.try_reserve(new_cap)?;
					heap.push_str(s.as_str());
					*self = TinyString::Heap(heap);
					Ok(())
				}
				Some(_) => Ok(()),
				// need some way to create a capacity overflow error
				None => String::new().try_reserve(usize::MAX),
			},
			TinyString::Heap(s) => s.try_reserve(additional),
		}
	}

	/// Tries to reserve the minimum capacity for exactly `additional` more elements to
	/// be inserted in the given `TinyString`. After calling `reserve_exact`,
	/// capacity will be greater than or equal to `self.len() + additional`.
	/// Does nothing if the capacity is already sufficient.
	///
	/// Note that the allocator may give the collection more space than it
	/// requests. Therefore, capacity can not be relied upon to be precisely
	/// minimal. Prefer [`try_reserve`] if future insertions are expected.
	///
	/// [`try_reserve`]: #method.try_reserve
	///
	/// # Errors
	///
	/// If the capacity overflows, or the allocator reports a failure, then an error
	/// is returned.
	///
	/// # Examples
	///
	/// ```
	/// # const N: usize = 1;
	/// # use tinyvec_string::TinyString;
	/// use std::collections::TryReserveError;
	///
	/// fn process_data(data: &str) -> Result<TinyString<[u8; N]>, TryReserveError> {
	///     let mut output = TinyString::new();
	///
	///     // Pre-reserve the memory, exiting if we can't
	///     output.try_reserve_exact(data.len())?;
	///
	///     // Now we know this can't OOM in the middle of our complex work
	///     output.push_str(data);
	///
	///     Ok(output)
	/// }
	/// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
	/// ```
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "rustc_1_57")))]
	#[cfg(feature = "rustc_1_57")]
	pub fn try_reserve_exact(
		&mut self,
		additional: usize,
	) -> Result<(), alloc::collections::TryReserveError> {
		match self {
			TinyString::Inline(s) => match s.len().checked_add(additional) {
				Some(new_cap) if new_cap > s.capacity() => {
					let mut heap = String::new();
					heap.try_reserve_exact(new_cap)?;
					heap.push_str(s.as_str());
					*self = TinyString::Heap(heap);
					Ok(())
				}
				Some(_) => Ok(()),
				// need some way to create a capacity overflow error
				None => String::new().try_reserve(usize::MAX),
			},
			TinyString::Heap(s) => s.try_reserve_exact(additional),
		}
	}

	/// Shrinks the capacity of this `TinyString` to match its length.
	///
	/// If the `TinyString` is on the heap, and the current length is less than
	/// or equal to its inline capacity, then the `TinyString` is made inline.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::from("foo");
	///
	/// s.reserve(100);
	/// assert!(s.capacity() >= 100);
	///
	/// s.shrink_to_fit();
	/// assert_eq!(5, s.capacity());
	/// ```
	pub fn shrink_to_fit(&mut self) {
		if self.is_heap() {
			if self.len() <= A::CAPACITY {
				*self = TinyString::Inline(ArrayString::from(self.as_str()));
			} else {
				match self {
					TinyString::Heap(s) => s.shrink_to_fit(),
					TinyString::Inline(_) => unreachable!(),
				}
			}
		}
	}

	/// Shrinks the capacity of this `TinyString` with a lower bound.
	///
	/// The capacity will remain at least as large as both the length, the
	/// supplied value, and the inline capacity.
	///
	/// If the `TinyString` is on the heap, and the new capacity is less than
	/// or equal to its inline capacity, then the `TinyString` is made inline.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 5]>::from("foo");
	///
	/// s.reserve(100);
	/// assert!(s.capacity() >= 100);
	///
	/// s.shrink_to(10);
	/// assert!(s.capacity() >= 10);
	/// s.shrink_to(0);
	/// assert!(s.capacity() >= 5);
	/// ```
	pub fn shrink_to(&mut self, min_capacity: usize) {
		if self.is_heap() {
			if self.len().max(min_capacity) <= A::CAPACITY {
				*self = TinyString::Inline(ArrayString::from(self.as_str()));
			} else {
				match self {
					TinyString::Heap(s) => s.shrink_to(min_capacity),
					TinyString::Inline(_) => unreachable!(),
				}
			}
		}
	}

	/// Appends a given string slice onto the end of this `TinyString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 6]>::from("foo");
	///
	/// s.push_str("bar");
	///
	/// assert_eq!("foobar", s);
	/// ```
	#[inline]
	pub fn push_str(&mut self, string: &str) {
		self.reserve(string.len());
		match self {
			TinyString::Inline(s) => s.push_str(string),
			TinyString::Heap(s) => s.push_str(string),
		}
	}

	/// Appends the given [`char`] to the end of this `TinyString`.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 6]>::from("abc");
	///
	/// s.push('1');
	/// s.push('2');
	/// s.push('3');
	///
	/// assert_eq!("abc123", s);
	/// ```
	#[inline]
	pub fn push(&mut self, ch: char) {
		self.reserve(ch.len_utf8());
		match self {
			TinyString::Inline(s) => s.push(ch),
			TinyString::Heap(s) => s.push(ch),
		}
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Shortens this `TinyString` to the specified length.
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
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let mut s = TinyString::<[u8; 5]>::from("hello");
		///
		/// s.truncate(2);
		///
		/// assert_eq!("he", s);
		/// ```
		#[inline]
		pub fn truncate(self: &mut Self, new_len: usize);
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Removes the last character from the string buffer and returns it.
		///
		/// Returns [`None`] if this `String` is empty.
		///
		/// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let mut s = TinyString::<[u8; 3]>::from("foo");
		///
		/// assert_eq!(s.pop(), Some('o'));
		/// assert_eq!(s.pop(), Some('o'));
		/// assert_eq!(s.pop(), Some('f'));
		///
		/// assert_eq!(s.pop(), None);
		/// ```
		#[inline]
		pub fn pop(self: &mut Self) -> Option<char>;
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Removes a [`char`] from this `String` at a byte position and returns it.
		///
		/// This is an `O(n)` operation, as it requires copying every element in the
		/// buffer.
		///
		/// # Panics
		///
		/// Panics if `idx` is larger than or equal to the `TinyString`'s length,
		/// or if it does not lie on a [`char`] boundary.
		///
		/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let mut s = TinyString::<[u8; 3]>::from("foo");
		///
		/// assert_eq!(s.remove(0), 'f');
		/// assert_eq!(s.remove(1), 'o');
		/// assert_eq!(s.remove(0), 'o');
		/// ```
		#[inline]
		pub fn remove(self: &mut Self, idx: usize) -> char;
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
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 9]>::from("f_o_ob_ar");
	///
	/// s.retain(|c| c != '_');
	///
	/// assert_eq!(s, "foobar");
	/// ```
	///
	/// The exact order may be useful for tracking external state, like an index.
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 5]>::from("abcde");
	/// let keep = [false, true, true, false, true];
	/// let mut i = 0;
	/// s.retain(|_| (keep[i], i += 1).0);
	/// assert_eq!(s, "bce");
	/// ```
	#[inline]
	pub fn retain<F>(&mut self, f: F)
	where
		F: FnMut(char) -> bool,
	{
		match self {
			TinyString::Inline(s) => s.retain(f),
			TinyString::Heap(s) => s.retain(f),
		}
	}

	/// Inserts a character into this `TinyString` at a byte position.
	///
	/// This is an `O(n)` operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `TinyString`'s length, or if it does not
	/// lie on a [`char`] boundary.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 3]>::new();
	///
	/// s.insert(0, 'f');
	/// s.insert(1, 'o');
	/// s.insert(2, 'o');
	///
	/// assert_eq!("foo", s);
	/// ```
	#[inline]
	pub fn insert(&mut self, idx: usize, ch: char) {
		self.reserve(ch.len_utf8());
		match self {
			TinyString::Inline(s) => s.insert(idx, ch),
			TinyString::Heap(s) => s.insert(idx, ch),
		}
	}

	/// Inserts a string slice into this `TinyString` at a byte position.
	///
	/// This is an `O(n)` operation as it requires copying every element in the
	/// buffer.
	///
	/// # Panics
	///
	/// Panics if `idx` is larger than the `String`'s length, or if it does not
	/// lie on a [`char`] boundary.
	///
	/// [`char`]: https://doc.rust-lang.org/std/primitive.char.html
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 6]>::from("bar");
	///
	/// s.insert_str(0, "foo");
	///
	/// assert_eq!("foobar", s);
	/// ```
	#[inline]
	pub fn insert_str(&mut self, idx: usize, string: &str) {
		self.reserve(string.len());
		match self {
			TinyString::Inline(s) => s.insert_str(idx, string),
			TinyString::Heap(s) => s.insert_str(idx, string),
		}
	}

	impl_mirrored! {
		type Mirror = TinyString;

		/// Truncates this `TinyString`, removing all contents.
		///
		/// While this means the `TinyString` will have a length of zero, it does
		/// not modify its capacity.
		///
		/// # Examples
		///
		/// ```
		/// # use tinyvec_string::TinyString;
		/// use std::convert::TryFrom;
		/// let mut s = TinyString::<[u8; 3]>::from("foo");
		///
		/// s.clear();
		///
		/// assert!(s.is_empty());
		/// assert_eq!(0, s.len());
		/// assert_eq!(3, s.capacity());
		/// ```
		#[inline]
		pub fn clear(self: &mut Self);
	}

	/// Creates a draining iterator that removes the specified range in the
	/// `TinyString` and yields the removed `chars`.
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
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut s = TinyString::<[u8; 23]>::from("α is alpha, β is beta");
	/// let beta_offset = s.find('β').unwrap_or(s.len());
	///
	/// // Remove the range up until the β from the string
	/// let t: TinyString<[u8; 23]> = s.drain(..beta_offset).collect();
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

	/// Move this `TinyString` to the heap.
	///
	/// Has no effect if this string is already on the heap.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 8]>::new();
	///
	/// assert!(s.is_inline());
	///
	/// s.move_to_the_heap();
	///
	/// assert!(s.is_heap());
	/// ```
	#[inline]
	pub fn move_to_the_heap(&mut self) {
		match self {
			TinyString::Inline(s) => {
				*self = TinyString::Heap(String::from(s.as_str()))
			}
			TinyString::Heap(_) => (),
		}
	}

	/// Removes the specified range in the string,
	/// and replaces it with the given string.
	/// The given string doesn't need to be the same length as the range.
	///
	/// # Panics
	///
	/// Panics if the starting point or end point do not lie on a [`char`]
	/// boundary, or if they're out of bounds.
	///
	/// # Examples
	///
	/// Basic usage:
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let mut s = TinyString::<[u8; 32]>::from("α is alpha, β is beta");
	/// let beta_offset = s.find('β').unwrap_or(s.len());
	///
	/// // Replace the range up until the β from the string
	/// s.replace_range(..beta_offset, "Α is capital alpha; ");
	/// assert_eq!(s, "Α is capital alpha; β is beta");
	/// ```
	#[inline]
	pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
	where
		R: RangeBounds<usize>,
	{
		match self {
			TinyString::Inline(s) => s.replace_range(range, replace_with),
			TinyString::Heap(s) => s.replace_range(range, replace_with),
		}
	}

	/// Splits the string into two at the given index.
	///
	/// Returns a new `TinyString`. `self` contains bytes `[0, at)`, and
	/// the returned `TinyString` contains bytes `[at, len)`. `at` must be on
	/// the boundary of a UTF-8 code point.
	///
	/// Both `self` and the returned `TinyString` will have the same capacity
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
	/// # use tinyvec_string::TinyString;
	/// use std::convert::TryFrom;
	/// let mut hello = TinyString::<[u8; 13]>::from("Hello, World!");
	/// let world = hello.split_off(7);
	/// assert_eq!(hello, "Hello, ");
	/// assert_eq!(world, "World!");
	/// ```
	#[inline]
	#[must_use = "use `.truncate()` if you don't need the other half"]
	pub fn split_off(&mut self, at: usize) -> TinyString<A> {
		match self {
			TinyString::Inline(s) => TinyString::Inline(s.split_off(at)),
			TinyString::Heap(s) => TinyString::Heap(s.split_off(at)),
		}
	}
}

impl<A: ByteArray> Deref for TinyString<A> {
	type Target = str;

	impl_mirrored! {
		type Mirror = TinyString;

		#[inline]
		fn deref(self: &Self) -> &str;
	}
}

impl<A: ByteArray> DerefMut for TinyString<A> {
	impl_mirrored! {
		type Mirror = TinyString;

		#[inline]
		fn deref_mut(self: &mut Self) -> &mut str;
	}
}

impl<A: ByteArray> fmt::Display for TinyString<A> {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(&**self, f)
	}
}

impl<A: ByteArray> fmt::Debug for TinyString<A> {
	#[inline]
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Debug::fmt(&**self, f)
	}
}

impl<A: ByteArray> Hash for TinyString<A> {
	#[inline]
	fn hash<H: Hasher>(&self, hasher: &mut H) {
		(**self).hash(hasher)
	}
}

impl<A: ByteArray + Clone> Clone for TinyString<A> {
	#[inline]
	fn clone(&self) -> Self {
		match self {
			TinyString::Inline(s) => TinyString::Inline(s.clone()),
			TinyString::Heap(s) => TinyString::Heap(s.clone()),
		}
	}

	#[inline]
	fn clone_from(&mut self, source: &Self) {
		match source {
			TinyString::Inline(s) => *self = TinyString::Inline(s.clone()),
			TinyString::Heap(s) => *self = TinyString::Heap(s.clone()),
		}
	}
}

impl<A: ByteArray, A2: ByteArray> FromIterator<TinyString<A2>>
	for TinyString<A>
{
	fn from_iter<I: IntoIterator<Item = TinyString<A2>>>(iter: I) -> Self {
		let mut buf = TinyString::new();
		buf.extend(iter);
		buf
	}
}

macro_rules! impl_from_iterator {
	($(#[$meta:meta])* $ty:ty) => {
		$(#[$meta])*
		#[allow(unused_lifetimes)]
		impl<'a, A: ByteArray> FromIterator<$ty>
			for TinyString<A>
		{
			fn from_iter<I: IntoIterator<Item = $ty>>(iter: I) -> Self {
				let mut buf = TinyString::new();
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

impl<A: ByteArray> Extend<char> for TinyString<A> {
	fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
		let iterator = iter.into_iter();
		iterator.for_each(move |c| self.push(c));
	}
}

impl<'a, A: ByteArray> Extend<&'a char> for TinyString<A> {
	fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
		self.extend(iter.into_iter().copied());
	}
}

impl<'a, A: ByteArray> Extend<&'a str> for TinyString<A> {
	fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(s));
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<A: ByteArray> Extend<String> for TinyString<A> {
	fn extend<I: IntoIterator<Item = String>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

impl<A: ByteArray, A2: ByteArray> Extend<TinyString<A2>> for TinyString<A> {
	fn extend<I: IntoIterator<Item = TinyString<A2>>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
impl<'a, A: ByteArray> Extend<Cow<'a, str>> for TinyString<A> {
	fn extend<I: IntoIterator<Item = Cow<'a, str>>>(&mut self, iter: I) {
		iter.into_iter().for_each(move |s| self.push_str(&s));
	}
}

macro_rules! impl_eq {
	($(#[$meta:meta])* $lhs:ty, $rhs: ty) => {
		$(#[$meta])*
		#[allow(unused_lifetimes)]
		impl<'a, 'b, A: ByteArray> PartialEq<$rhs> for $lhs {
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
		impl<'a, 'b, A: ByteArray> PartialEq<$lhs> for $rhs {
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

impl_eq! { TinyString<A>, str }
impl_eq! { TinyString<A>, &'a str }
impl_eq! {
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
	#[cfg(feature = "alloc")]
	TinyString<A>, Cow<'a, str>
}
impl_eq! {
	#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
	#[cfg(feature = "alloc")]
	TinyString<A>, String
}

impl<A1, A2> PartialEq<TinyString<A1>> for TinyString<A2>
where
	A1: ByteArray,
	A2: ByteArray,
{
	#[inline]
	fn eq(&self, other: &TinyString<A1>) -> bool {
		PartialEq::eq(&self[..], &other[..])
	}
	#[inline]
	fn ne(&self, other: &TinyString<A1>) -> bool {
		PartialEq::ne(&self[..], &other[..])
	}
}

/// Implements the `+` operator for concatenating two strings.
///
/// # Examples
///
/// ```
/// # use tinyvec_string::TinyString;
/// use std::convert::TryFrom;
/// let a = TinyString::<[u8; 13]>::from("Hello, ");
/// let b = "World!";
/// let c = a + b;
/// assert_eq!(c, "Hello, World!");
/// ```
impl<A: ByteArray> Add<&str> for TinyString<A> {
	type Output = TinyString<A>;

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
/// # Examples
///
/// ```
/// # use tinyvec_string::TinyString;
/// use std::convert::TryFrom;
/// let mut a = TinyString::<[u8; 13]>::from("Hello, ");
/// let b = "World!";
/// a += b;
/// assert_eq!(a, "Hello, World!");
/// ```
///
/// [`push_str`]: TinyString.html#method.push_str
impl<A: ByteArray> AddAssign<&str> for TinyString<A> {
	#[inline]
	fn add_assign(&mut self, other: &str) {
		self.push_str(other);
	}
}

impl<A: ByteArray> ops::Index<ops::Range<usize>> for TinyString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::Range<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: ByteArray> ops::Index<ops::RangeTo<usize>> for TinyString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeTo<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: ByteArray> ops::Index<ops::RangeFrom<usize>> for TinyString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeFrom<usize>) -> &str {
		&self[..][index]
	}
}

impl<A: ByteArray> ops::Index<ops::RangeFull> for TinyString<A> {
	type Output = str;

	impl_mirrored! {
		type Mirror = TinyString;

		#[inline]
		fn index(self: &Self, index: ops::RangeFull) -> &str;
	}
}

impl<A: ByteArray> ops::Index<ops::RangeInclusive<usize>> for TinyString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeInclusive<usize>) -> &str {
		Index::index(&**self, index)
	}
}

impl<A: ByteArray> ops::Index<ops::RangeToInclusive<usize>> for TinyString<A> {
	type Output = str;

	#[inline]
	fn index(&self, index: ops::RangeToInclusive<usize>) -> &str {
		Index::index(&**self, index)
	}
}

impl<A: ByteArray> ops::IndexMut<ops::Range<usize>> for TinyString<A> {
	#[inline]
	fn index_mut(&mut self, index: ops::Range<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: ByteArray> ops::IndexMut<ops::RangeTo<usize>> for TinyString<A> {
	#[inline]
	fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: ByteArray> ops::IndexMut<ops::RangeFrom<usize>> for TinyString<A> {
	#[inline]
	fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut str {
		&mut self[..][index]
	}
}

impl<A: ByteArray> ops::IndexMut<ops::RangeFull> for TinyString<A> {
	impl_mirrored! {
		type Mirror = TinyString;

		#[inline]
		fn index_mut(self: &mut Self, index: ops::RangeFull) -> &mut str;
	}
}

impl<A: ByteArray> ops::IndexMut<ops::RangeInclusive<usize>> for TinyString<A> {
	#[inline]
	fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut str {
		IndexMut::index_mut(&mut **self, index)
	}
}

impl<A: ByteArray> ops::IndexMut<ops::RangeToInclusive<usize>>
	for TinyString<A>
{
	#[inline]
	fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut str {
		IndexMut::index_mut(&mut **self, index)
	}
}

impl<A: ByteArray> AsRef<str> for TinyString<A> {
	#[inline]
	fn as_ref(&self) -> &str {
		&*self
	}
}

impl<A: ByteArray> AsMut<str> for TinyString<A> {
	#[inline]
	fn as_mut(&mut self) -> &mut str {
		&mut *self
	}
}

impl<A: ByteArray> AsRef<[u8]> for TinyString<A> {
	#[inline]
	fn as_ref(&self) -> &[u8] {
		self.as_bytes()
	}
}

impl<'a, A: ByteArray> From<&'a str> for TinyString<A> {
	fn from(s: &'a str) -> Self {
		unsafe {
			let mut tv = TinyVec::from_array_len(A::DEFAULT, 0);
			tv.extend(s.as_bytes().iter().copied());
			TinyString::from_utf8_unchecked(tv)
		}
	}
}

impl<'a, A: ByteArray> From<&'a mut str> for TinyString<A> {
	fn from(s: &'a mut str) -> Self {
		TinyString::from(&*s)
	}
}

impl<A: ByteArray> From<char> for TinyString<A> {
	fn from(c: char) -> Self {
		let mut buf = [0u8; 4];
		let s = c.encode_utf8(&mut buf);
		TinyString::from(s)
	}
}

impl<'a, A: ByteArray> From<&'a char> for TinyString<A> {
	fn from(c: &'a char) -> Self {
		TinyString::from(*c)
	}
}

impl<'a, A: ByteArray> From<&'a String> for TinyString<A> {
	fn from(s: &'a String) -> Self {
		TinyString::from(s.as_str())
	}
}

impl<A: ByteArray> From<String> for TinyString<A> {
	/// This converts the `String` into a heap-allocated `TinyVec` to avoid
	/// unnecessary allocations.
	fn from(s: String) -> Self {
		unsafe {
			TinyString::from_utf8_unchecked(TinyVec::Heap(s.into_bytes()))
		}
	}
}

impl<'a, A: ByteArray> From<Cow<'a, str>> for TinyString<A> {
	/// If the `Cow` is `Owned`, then the `String` is converted into a
	/// heap-allocated `TinyVec` to avoid unnecessary allocations. If it is
	/// `Borrowed`, then an allocation may be made.
	fn from(s: Cow<'a, str>) -> Self {
		match s {
			Cow::Borrowed(s) => TinyString::from(s),
			Cow::Owned(s) => TinyString::from(s),
		}
	}
}

impl<A: ByteArray> FromStr for TinyString<A> {
	type Err = Infallible;
	#[inline]
	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(TinyString::from(s))
	}
}

impl<A: ByteArray> fmt::Write for TinyString<A> {
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

#[cfg_attr(docs_rs, doc(cfg(target_feature = "serde")))]
#[cfg(feature = "serde")]
impl<A: ByteArray> serde::Serialize for TinyString<A> {
	/// Serializes the string.
	///
	/// # Example
	///
	/// ```
	/// # use tinyvec_string::ArrayString;
	/// let s = ArrayString::<[u8; 5]>::from("hello");
	/// let json = serde_json::to_string(&s);
	/// assert!(json.is_ok());
	/// assert_eq!(json.unwrap(), "\"hello\"");
	/// ```
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: serde::Serializer,
	{
		serializer.serialize_str(self.as_str())
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "serde")))]
#[cfg(feature = "serde")]
impl<'de, A: ByteArray> serde::Deserialize<'de> for TinyString<A> {
	/// Deserializes into a `TinyString`.
	///
	/// # Example
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// let src = "\"hello\"";
	/// let parsed = serde_json::from_str::<TinyString<[u8; 5]>>(src);
	/// assert!(parsed.is_ok());
	/// assert_eq!("hello", parsed.unwrap());
	/// ```
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: serde::Deserializer<'de>,
	{
		use core::marker::PhantomData;

		struct TinyStringVisitor<A>(PhantomData<fn() -> A>);

		impl<'de, A: ByteArray> serde::de::Visitor<'de> for TinyStringVisitor<A> {
			type Value = TinyString<A>;

			fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
				write!(f, "a string up to length {}", A::CAPACITY)
			}

			fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
			where
				E: serde::de::Error,
			{
				Ok(TinyString::from(v))
			}
		}

		deserializer.deserialize_str(TinyStringVisitor(PhantomData))
	}
}

/// A possible error value when converting an [`TinyString`] from a UTF-8 byte
/// vector.
///
/// This type is the error type for the [`from_utf8`] method on `TinyString`.
/// The [`into_bytes`] method will give back the byte vector that was used in
/// the conversion attempt.
///
/// [`from_utf8`]: enum.TinyString.html#method.from_utf8
/// [`TinyString`]: enum.TinyString.html
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
/// # use tinyvec_string::TinyString;
/// use tinyvec::{tiny_vec, TinyVec};
/// // some invalid bytes, in a vector
/// let bytes: TinyVec<[u8; 2]> = tiny_vec![0, 159];
///
/// let value = TinyString::from_utf8(bytes);
///
/// assert_eq!(Err(tiny_vec![0, 159]), value.map_err(|e| e.into_bytes()));
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct FromUtf8Error<A: ByteArray> {
	vec: TinyVec<A>,
	error: Utf8Error,
}

impl<A: ByteArray> FromUtf8Error<A> {
	/// Returns a slice of [`u8`]s bytes that were attempted to convert to an
	/// `TinyString`.
	///
	/// # Examples
	///
	/// ```
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	/// // some invalid bytes, in a vector
	/// let bytes: TinyVec<[u8; 2]> = tiny_vec![0, 159];
	///
	/// let value = TinyString::from_utf8(bytes);
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
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	/// // some invalid bytes, in a vector
	/// let bytes: TinyVec<[u8; 2]> = tiny_vec![0, 159];
	///
	/// let value = TinyString::from_utf8(bytes);
	///
	/// assert_eq!(tiny_vec![0, 159], value.unwrap_err().into_bytes());
	/// ```
	pub fn into_bytes(self) -> TinyVec<A> {
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
	/// # use tinyvec_string::TinyString;
	/// use tinyvec::{tiny_vec, TinyVec};
	/// // some invalid bytes, in a vector
	/// let bytes: TinyVec<[u8; 2]> = tiny_vec![0, 159];
	///
	/// let error = TinyString::from_utf8(bytes).unwrap_err().utf8_error();
	///
	/// // the first byte is invalid here
	/// assert_eq!(1, error.valid_up_to());
	/// ```
	pub fn utf8_error(&self) -> Utf8Error {
		self.error
	}
}

impl<A: ByteArray> fmt::Debug for FromUtf8Error<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("FromUtf8Error")
			.field("vec", &self.vec)
			.field("error", &self.error)
			.finish()
	}
}

impl<A: ByteArray> fmt::Display for FromUtf8Error<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		fmt::Display::fmt(&self.error, f)
	}
}

#[cfg_attr(docs_rs, doc(cfg(target_feature = "std")))]
#[cfg(feature = "std")]
impl<A: ByteArray> std::error::Error for FromUtf8Error<A> {}

/// A draining iterator for [`TinyString`].
///
/// This struct is created by the [`drain`] method on [`TinyString`]. See its
/// documentation for more.
///
/// [`drain`]: enum.TinyString.html#method.drain
/// [`TinyString`]: enum.TinyString.html
pub struct Drain<'a, A: ByteArray> {
	/// Will be used as &'a mut TinyString in the destructor
	string: *mut TinyString<A>,
	/// Start of part to remove
	start: usize,
	/// End of part to remove
	end: usize,
	/// Current remaining range to remove
	iter: Chars<'a>,
}

impl<A: ByteArray> fmt::Debug for Drain<'_, A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.pad("Drain { .. }")
	}
}

unsafe impl<A: ByteArray> Send for Drain<'_, A> {}
unsafe impl<A: ByteArray> Sync for Drain<'_, A> {}

impl<A: ByteArray> Drop for Drain<'_, A> {
	fn drop(&mut self) {
		unsafe {
			// Use backing drain. "Reaffirm" the bounds checks to avoid
			// panic code being inserted again.
			let this = &mut *self.string;
			match this {
				TinyString::Inline(s) => {
					let this_vec = s.as_mut_vec();
					if self.start <= self.end && self.end <= this_vec.len() {
						drop(this_vec.drain(self.start..self.end))
					}
				}
				TinyString::Heap(s) => {
					let this_vec = s.as_mut_vec();
					if self.start <= self.end && self.end <= this_vec.len() {
						drop(this_vec.drain(self.start..self.end))
					}
				}
			}
		}
	}
}

impl<A: ByteArray> Iterator for Drain<'_, A> {
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

impl<A: ByteArray> DoubleEndedIterator for Drain<'_, A> {
	#[inline]
	fn next_back(&mut self) -> Option<char> {
		self.iter.next_back()
	}
}

impl<A: ByteArray> FusedIterator for Drain<'_, A> {}
