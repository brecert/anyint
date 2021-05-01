#![allow(incomplete_features)]
#![feature(
    decl_macro,
    const_fn,
    const_trait_impl,
    const_refs_to_cell,
    associated_type_defaults,
    specialization,
    int_bits_const,
    extended_key_value_attributes
)]

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
