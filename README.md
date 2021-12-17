[![crates.io](https://img.shields.io/crates/v/tinyvec_string.svg)](https://crates.io/crates/tinyvec_string)
[![docs.rs](https://docs.rs/tinyvec_string/badge.svg)](https://docs.rs/tinyvec_string/)
![Tests](https://github.com/ThatsNoMoon/tinyvec_string/workflows/Tests/badge.svg)

# tinyvec_string

[`tinyvec`](https://github.com/Lokathor/tinyvec) based string types.

See [the docs.rs documentation](https://docs.rs/tinyvec_string/)

`tinyvec_string` provides two string types:
* `ArrayString`, a string backed by a fixed-size array on the stack,
  using `ArrayVec`
* `TinyString`, a string backed by either a fixed-size array on the stack
  or a `Vec` on the heap

## Features

Like `tinyvec`, `tinyvec_string` is `no_std` by default.

`ArrayString` has no dependencies (other than `tinyvec` and `core`).

`TinyString` requires the the `alloc` cargo feature to be enabled because
it has a dependency on `alloc`:

```toml
[dependencies]
tinyvec_string = { version = "0.1.0", features = ["alloc"] }
```

Error types implement `std::error::Error` when the `std` feature is
enabled.

The `rustc_1_40` feature enables `tinyvec`'s `rustc_1_40` feature, which enables
some optimizations for Rust versions >= 1.40.

The `rustc_1_55` feature enables usage of const generics to allow usage of
backing arrays of any size.

## Safety

This crate strives to be as safe as possible. Almost all internal `unsafe`
code is copied verbatim from `std`'s `String` implementation for maximum
reliability and performance.

## MSRV

Like `tinyvec`, `tinyvec_string` (without `rustc` version features) supports
Rust 1.34+. The `alloc` feature requires Rust 1.36+.

## Contributing

Feel free to open an issue if you have a problem, or open a pull request if you
have a solution. Also feel free to reach me on
[the Rust Community Discord Server](https://discord.gg/aVESxV8) @ThatsNoMoon#0175.

## License

`tinyvec_string` is dual-licensed under Apache-2.0 and MIT. Large sections of
code, documentation, and tests were copied verbatim or copied and modified from
[rust-lang/rust](https://github.com/rust-lang/rust); copyright for such content
belongs to the original author.
