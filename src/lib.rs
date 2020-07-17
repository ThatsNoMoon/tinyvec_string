//! [`tinyvec`] based string types.
//!
//! `tinyvec_string` provides two string types:
//! * [`ArrayString`], a string backed by a fixed-size array on the stack,
//!   using [`ArrayVec`]
//! * [`TinyString`], a string backed by either a fixed-size array on the stack
//!   or a [`Vec`] on the heap, using [`TinyVec`]
//!
//! ## Features
//!
//! Like `tinyvec`, `tinyvec_string` is `no_std` by default.
//!
//! `ArrayString` has no dependencies (other than `tinyvec` and `core`).
//!
//! `TinyString` requires the the `alloc` cargo feature to be enabled because
//! it has a dependency on `alloc`:
//!
//! ```toml
//! [dependencies]
//! tinyvec_string = { version = "0.1.0", features = ["alloc"] }
//! ```
//!
//! Error types implement [`std::error::Error`] when the `std` feature is
//! enabled.
//!
//! ## Safety
//!
//! This crate strives to be as safe as possible. Almost all internal `unsafe`
//! code is copied verbatim from `std`'s `String` implementation for maximum
//! reliability and performance.
//!
//! [`tinyvec`]: tinyvec.html
//! [`ArrayString`]: arraystring/struct.ArrayString.html
//! [`TinyString`]: tinystring/struct.TinyString.html
//! [`ArrayVec`]: tinyvec/struct.ArrayVec.html
//! [`TinyVec`]: tinyvec/enum.TinyVec.html
//! [`Array`]: tinyvec/trait.Array.html
//! [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docs_rs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod arraystring;

pub use arraystring::ArrayString;

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
pub mod tinystring;

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
pub use tinystring::TinyString;

pub mod tinyvec;

pub mod bytearray;
