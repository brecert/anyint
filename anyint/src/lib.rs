// todo: no std
// todo: unstable feature flags
use std::convert::{From, TryFrom};
use std::fmt::{self, Display};
use thiserror::Error;

pub use anyint_macros::{n};

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

// todo: Const trait implementations
pub trait NonStandardInteger<T, const BITS: u32, const SIGNED: bool> {
    /// Represents if this integer type is considered to be signed or not.
    const SIGNED: bool = SIGNED;

    /// The size of this integer type in bits.
    const BITS: u32 = BITS;

    /// The smallest value that can be represented by this integer type.
    const MIN: T;

    /// The largest value that can be represented by this integer type.
    const MAX: T;
}

/// An integer representation that can hold `BITS` amount of information for the given type `T`.
#[repr(transparent)]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct int<T, const BITS: u32>(T);

impl<T: Display, const BITS: u32> Display for int<T, BITS> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

// decl 1.0 for supporting older rust

#[doc(hidden)]
#[macro_export]
macro_rules! impl_common {
    ($ty: ty) => {
        impl<const BITS: u32> int<$ty, BITS> {
            /// Returns the largest value that can be represented by this integer type.
            #[inline]
            pub const fn max_value() -> Self {
                Self(Self::MAX)
            }

            pub fn bits(self) -> u32 {
                Self::BITS
            }

            pub fn repr(self) -> u32 {
                <$ty>::BITS
            }

            /// Returns the smallest value that can be represented by this integer type.
            #[inline]
            pub const fn min_value() -> Self {
                Self(Self::MIN)
            }

            /// Convert a `$ty` into the target without bounds checking
            #[inline]
            pub const unsafe fn from_unchecked(data: $ty) -> Self {
                Self(data)
            }

            /// Convert a `$ty` into the target. Only the `BITS` amount are kept.
            #[inline]
            pub const fn from_lossy(data: $ty) -> Self {
                Self(data & Self::MAX)
            }
        }

        impl<const BITS: u32> From<int<$ty, BITS>> for $ty {
            #[inline]
            fn from(data: int<$ty, BITS>) -> $ty {
                data.0
            }
        }

        impl<const BITS: u32> TryFrom<$ty> for int<$ty, BITS> {
            type Error = OutOfRangeIntError;

            fn try_from(data: $ty) -> Result<Self, Self::Error> {
                if data > Self::MAX {
                    Err(OutOfRangeIntError)
                } else {
                    Ok(Self(data))
                }
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! impl_nonstandard_int {
    (unsigned: $ty: ty) => {
        impl<const BITS: u32> NonStandardInteger<$ty, BITS, false> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS) - 1;
            const MIN: $ty = 0;
        }

        impl_common!($ty);
    };
    (signed: $ty: ty) => {
        impl<const BITS: u32> NonStandardInteger<$ty, BITS, true> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS.saturating_sub(1)) - 1;
            const MIN: $ty = !Self::MAX;
        }

        impl_common!($ty);
    };
}

impl_nonstandard_int!(unsigned: u8);
impl_nonstandard_int!(unsigned: u16);
impl_nonstandard_int!(unsigned: u32);
impl_nonstandard_int!(unsigned: u64);
impl_nonstandard_int!(unsigned: u128);
impl_nonstandard_int!(unsigned: usize);

impl_nonstandard_int!(signed: i8);
impl_nonstandard_int!(signed: i16);
impl_nonstandard_int!(signed: i32);
impl_nonstandard_int!(signed: i64);
impl_nonstandard_int!(signed: i128);
impl_nonstandard_int!(signed: isize);

#[cfg(test)]
mod test {
    use super::*;
    use std::convert::TryInto;

    // #[test]
    // #[ignore = "not yet implemented due to rust's current type system"]
    // fn test_invalid_bits_size() {
    //     let _ = int::<u8, 8>::MAX;
    // }

    mod macros {
        use super::*;

        #[test]
        fn smoketest() {
            let x = n!(-32i21);
            dbg!(x, x.bits(), x.repr());
        }
    }

    mod unsigned {
        use super::*;

        #[test]
        fn max() {
            assert_eq!(int::<u8, 6>::MAX, 63);
        }

        #[test]
        fn min() {
            assert_eq!(int::<u8, 6>::MIN, 0);
        }

        #[test]
        fn bits() {
            assert_eq!(int::<u8, 6>::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(int::<u8, 6>::max_value(), int::<u8, 6>(63));
        }

        #[test]
        fn min_value() {
            assert_eq!(int::<u8, 6>::min_value(), int::<u8, 6>(0));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value = int::<u8, 6>::from_unchecked(u8::MAX);
                let value_u8: u8 = value.into();
                assert_eq!(value_u8, 255);
            }
        }

        #[test]
        fn from_lossy() {
            let value = int::<u8, 6>::from_lossy(u8::MAX);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 63);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: int<u8, 6> = int(15);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 15);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<int<u8, 6>, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(int::<u8, 6>(15)));
            let value: Result<int<u8, 6>, OutOfRangeIntError> = 64.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }
    }

    mod signed {
        use super::*;

        #[test]
        fn max() {
            assert_eq!(int::<i8, 6>::MAX, 31);
        }

        #[test]
        fn min() {
            assert_eq!(int::<i8, 6>::MIN, -32);
        }

        #[test]
        fn bits() {
            assert_eq!(int::<i8, 6>::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(int::<i8, 6>::max_value(), int::<i8, 6>(31));
        }

        #[test]
        fn min_value() {
            assert_eq!(int::<i8, 6>::min_value(), int::<i8, 6>(-32));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value = int::<i8, 6>::from_unchecked(i8::MAX);
                let value_i8: i8 = value.into();
                assert_eq!(value_i8, 127);
            }
        }

        #[test]
        fn from_lossy() {
            let value: int<i8, 6> = int::<i8, 6>::from_lossy(i8::MAX);
            let value_i8: i8 = value.into();
            assert_eq!(value_i8, 31);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: int<i8, 6> = int(15);
            let value_i8: i8 = value.into();
            assert_eq!(value_i8, 15);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<int<i8, 6>, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(int::<i8, 6>(15)));
            let value: Result<int<i8, 6>, OutOfRangeIntError> = 32.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }
    }
}
