use std::num::IntErrorKind;
use thiserror::Error;

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
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
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub enum ParseIntError {
    /// Value being parsed is empty.
    #[error("cannot parse integer from empty string")]
    Empty,

    /// Contains an invalid digit in its context.
    #[error("invalid digit found in string")]
    InvalidDigit,

    /// Value was too large or small to store in the target type.
    #[error("{0}")]
    OutOfRange(OutOfRangeIntError),

    #[error("Unknown parsing error.")]
    /// An unknown error, this should never happen.
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
