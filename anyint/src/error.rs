use core::num::IntErrorKind;

#[cfg(displaydoc)]
use displaydoc::Display;

/// The error type returned when a checked [`int`](anyint::int) conversion fails.
#[cfg_attr(
    std,
    error("out of range type conversion attempted"),
    derive(thiserror::Error)
)]
#[cfg_attr(displaydoc, derive(Display))]
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum OutOfRangeIntError {
    /// Integer is too large to store in target integer type.
    PosOverflow,
    /// Integer is too small to store in target integer type.
    NegOverflow,
}

impl From<OutOfRangeIntError> for ParseIntError {
    fn from(err: OutOfRangeIntError) -> Self {
        ParseIntError::OutOfRange(err)
    }
}

/// Enum to store the various types of errors that can cause parsing an integer to fail.
#[cfg_attr(std, derive(thiserror::Error))]
#[cfg_attr(displaydoc, derive(Display))]
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum ParseIntError {
    /// cannot parse integer from empty string
    Empty,

    /// invalid digit found in string
    InvalidDigit,

    /// Value {0} was too large or small to store in the target type.
    OutOfRange(OutOfRangeIntError),

    /// Unknown parsing error, this should never happen.
    Unknown,
}

impl From<IntErrorKind> for ParseIntError {
    fn from(kind: IntErrorKind) -> Self {
        match kind {
            IntErrorKind::Empty => ParseIntError::Empty,
            IntErrorKind::InvalidDigit => ParseIntError::InvalidDigit,
            IntErrorKind::NegOverflow => ParseIntError::OutOfRange(OutOfRangeIntError::NegOverflow),
            IntErrorKind::PosOverflow => ParseIntError::OutOfRange(OutOfRangeIntError::PosOverflow),
            _ => ParseIntError::Unknown,
        }
    }
}
