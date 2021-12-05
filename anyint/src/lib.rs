#![cfg_attr(not(feature = "std"), no_std)]
#![allow(incomplete_features)]
#![deny(missing_docs, unused_features)]
#![feature(
    test,
    decl_macro,
    const_panic,
    const_trait_impl,
    const_refs_to_cell,
    const_fn_trait_bound,
    associated_type_defaults,
    result_flattening
)]

//! Anyint provides traits and structs for working with integers of any bit size

extern crate self as anyint;

/// Restrict and contrain values.
pub mod clamp;

/// Conversion types intented to be used with [`int`].
pub mod convert;

/// Struct implementation for [`NonStandardInteger`](non_standard_integer::NonStandardInteger)
pub mod integer;

/// Traits for implementing a non standard integer.
pub mod non_standard_integer;

/// Error types relating to integers.
pub mod error;

pub mod macros;

/// Implementations of traits from the [`num-traits`] crate
#[cfg(feature = "num")]
mod num;

mod ops;

#[cfg(test)]
mod bench;

/// The purpose of this module is to alleviate imports of many common [`int`] traits.
///
/// ```
/// use anyint::prelude::*;
///
/// let x: int<u8, 6> = int::new(20);
/// assert_eq!(x.value(), 20);
///
/// let y: int<i8, 6> = int::from_wrapping(34);
/// assert_eq!(y.value(), -30);
/// ```
pub mod prelude {
    // todo: no std
    // todo: unstable feature flags
    pub use super::convert::*;
    pub use super::integer::int;
    pub use super::non_standard_integer::*;
}

pub use integer::int;
