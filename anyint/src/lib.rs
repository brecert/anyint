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

/// Conversion types meant for `int`.
pub mod convert;

/// Struct implementation for `NonStandardInteger`
pub mod integer;

/// Traits for implementing a non standard integer.
pub mod non_standard_integer;

/// Error types relating to integers.
pub mod error;

/// Implementations of traits from the `num-traits` crate
#[cfg(feature = "num")]
mod num;

mod ops;

#[cfg(test)]
mod bench;

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

#[cfg(test)]
mod test {
    use super::*;
    use anyint_macros::n;
    use prelude::*;

    mod macros {
        use super::*;

        #[test]
        fn n_macro_uint() {
            assert_eq!(n!(0u6), int::<u8, 6>::new(0));
            assert_eq!(n!(63u6), int::<u8, 6>::new(63));
        }

        #[test]
        fn n_macro_sint() {
            assert_eq!(n!(31i6), int::<i8, 6>::new(31));
            assert_eq!(n!(-32i6), int::<i8, 6>::new(-32));
        }
    }
}

#[cfg(doctest)]
mod doctest {
    // TODO: test compiler errors that are generated to make sure they are accurate

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = n!(64u6);
    /// ```
    pub struct MacroOnlyTakesValidPositiveUInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = n!(-1u6);
    /// ```
    pub struct MacroOnlyTakesValidNegativeUInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = n!(32i6);
    /// ```
    pub struct MacroOnlyTakesValidPositiveSInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = n!(-33i6);
    /// ```
    pub struct MacroOnlyTakesValidNegativeSInt;
}
