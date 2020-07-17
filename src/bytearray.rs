//! Trait for byte arrays.

/// An array type containing bytes.
///
/// Because `tinyvec_string` has `unsafe` and `tinyvec` doesn't, this trait is
/// required for soundness. `unsafe` code can depend on an `unsafe` trait, and
/// `tinyvec::Array` is not `unsafe`.
///
/// The provided implementations of `ByteArray` for various sizes of `[u8; N]`
/// follow this trait's contract, and it shouldn't be necessary to add
/// implementations for other types in most cases.
///
/// Implementations are provided for `[u8; N]` for `N <= 32` and powers of 2
/// <= 4096. Other implementations could be provided on request.
///
/// # Safety
/// Any types that implement this trait must have [`tinyvec::Array`]
/// implementations that always return the same slices; i.e. between calls
/// of `as_slice` or `as_slice_mut`, the implementation of the trait must not
/// modify the contents of the slice (directly or indirectly) or return a slice
/// with different contents. They must also always return slices with a length
/// of `CAPACITY`.
///
/// Any implementations must also follow the stated contract of `DEFAULT`.
///
/// Any implementations that do not follow the above may cause memory safety
/// errors within `ArrayString` or `TinyString`.
///
/// [`tinyvec::Array`]: ../tinyvec/trait.Array.html
pub unsafe trait ByteArray: tinyvec::Array<Item = u8> {
	/// Default value of the array.
	///
	/// This MUST be an array with length `CAPACITY` with all zero elements.
	const DEFAULT: Self;
}

macro_rules! impl_bytearray_for_len {
  ($($len:expr),+ $(,)?) => {
	$(unsafe impl ByteArray for [u8; $len] {
		const DEFAULT: Self = [0u8; $len];
	})+
  }
}

impl_bytearray_for_len! {
	0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 64, 128, 256, 512, 1024, 2048,
	4096,
}
