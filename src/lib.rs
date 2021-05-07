#![allow(incomplete_features)]
#![deny(missing_docs, unused_features)]
#![feature(
    decl_macro,
    const_fn,
    const_trait_impl,
    const_refs_to_cell,
    associated_type_defaults,
    int_bits_const,
    extended_key_value_attributes,
    int_error_matching,
    result_flattening
)]

//! Anyint provides traits and structs for working with integers of any bit size

/// Restrict and contrain values.
pub mod clamp;

/// Conversion types meant for `int`.
pub mod convert;

/// Struct implementation for `NonStandardInteger`
pub mod integer;

/// Traits for implementing a non standard integer.
pub mod non_standard_integer;

/// Error types relating to integers.
pub mod error;

mod ops;

/// The purpose of this module is to alleviate imports of many common `int` traits.
///
/// ```
/// use anyint::prelude::*;
///
/// let x: int<u8, 6> = int::new(20);
/// assert_eq!(x.val(), 20);
///
/// let y: int<i8, 6> = int::from_wrapping(34);
/// assert_eq!(y.val(), -30);
/// ```
pub mod prelude {
    // todo: no std
    // todo: unstable feature flags
    pub use super::convert::*;
    pub use super::integer::int;
    pub use super::non_standard_integer::*;
}
