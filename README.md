# anyint

> anyint provides traits and structs for working with integers of any bit size

This readme is lacking.

The library however, is not lacking in documentation.

```rust
use anyint::prelude::*;
use anyint::macros::int;

assert_eq!(int!(0u6), int::<u8, 6>::new(0));
assert_eq!(int!(-32i6), int::<i8, 6>::new(-32));

let num = int!(63u6).wrapping_add(int!(3u6));
assert_eq!(num.value(), 2);
```
