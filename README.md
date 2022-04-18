# anyint

anyint provides traits and structs for working with integers of any bit size

## Documentation

This readme is lacking.

The library however, should not be lacking in documentation.

## Example

```rust
use anyint::prelude::*;
use anyint::macros::{Int, int};

assert_eq!(int!(0u6), int::<u8, 6>::new(0));
assert_eq!(int!(-32i6), int::<i8, 6>::new(-32));

let num = int!(63u6).wrapping_add(int!(3u6));
assert_eq!(num.value(), 2);

fn add(a: u16, b: u16) -> Int![u12] {
  int::new(a).wrapping_add(int::new(b))
}
assert_eq!(add(4000, 96), int::new(0));
```
