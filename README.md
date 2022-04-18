# anyint — any bit sized integers

[![Latest Version](https://img.shields.io/crates/v/anyint.svg)](https://crates.io/crates/anyint)
[![Rust Documentation](https://img.shields.io/badge/api-rustdoc-blue.svg)](https://docs.rs/anyint)

This library provides traits and structs for working with integers of any bit size.

*Compiler support: tested with rustc 1.61.0 nightly, unsure about support on lower versions*

### Example

```rust
use anyint::prelude::*;
use anyint::macros::{Int, int};

// int macro to make working with the types easier
assert_eq!(int!(0u6), int::<u8, 6>::new(0));
assert_eq!(int!(-32i6), int::<i8, 6>::new(-32));

// many of the same methods that the standard library integers have
let num = int!(63u6).wrapping_add(int!(3u6));
assert_eq!(num.0, 2);

// Int type macro to make working with the types easier
fn add(a: u16, b: u16) -> Int![u12] {
  int::new(a) + int::new(b)
}
assert_eq!(add(5, 10), int::new(15));
```

### Details / Notes

The underlying representation of your integer will be what is provided for the `anyint::int` struct.

This is to keep performance reasonable and the implementations simple.

Most of the common methods that std integers have should also be implemented here, if there's any that's missing feel free to create an issue about it.

### FAQ

1. **Is this crate `no_std` compatable?**
    * Yes! Just add `default-features = false`.


<!-- This readme is heavily inspired by yaahc's and dtolnay's crate READMEs, thank you! -->