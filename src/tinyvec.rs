//! Re-exports from `tinyvec`.
//!
//! You can see `tinyvec`'s crate documentation [here](https://docs.rs/tinyvec/0.3/tinyvec/).

pub use tinyvec::{array_vec, Array, ArrayVec};

#[cfg_attr(docs_rs, doc(cfg(target_feature = "alloc")))]
#[cfg(feature = "alloc")]
pub use tinyvec::{tiny_vec, TinyVec};
