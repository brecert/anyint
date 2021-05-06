#![allow(incomplete_features)]
#![deny(missing_docs)]
#![feature(
    decl_macro,
    const_fn,
    const_trait_impl,
    const_refs_to_cell,
    associated_type_defaults,
    specialization,
    int_bits_const,
    extended_key_value_attributes,
    int_error_matching,
    result_flattening,
    const_trait_bound_opt_out
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
mod ops;

// todo: no std
// todo: unstable feature flags
pub use crate::convert::*;
pub use crate::integer::*;
pub use crate::non_standard_integer::*;
