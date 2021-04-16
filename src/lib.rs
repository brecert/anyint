#![allow(incomplete_features)]
#![feature(
    decl_macro,
    const_fn,
    const_trait_impl,
    const_refs_to_cell,
    associated_type_defaults,
    specialization
)]

// todo: no std
// todo: unstable feature flags
use std::convert::{From, TryFrom};
use std::fmt::{self, Display};
use std::ops::Range;
use thiserror::Error;

const fn clamp<T: PartialOrd + Copy>(range: &std::ops::Range<T>, val: T) -> T {
    if val < range.start {
        return range.start;
    }
    if val > range.end {
        return range.end;
    }
    return val;
}

trait Clamp<T> {
    type Output = T;
    fn clamp(&self, lhs: T) -> Self::Output;
}

impl<T: PartialOrd + Copy> const Clamp<T> for Range<T> {
    fn clamp(&self, val: T) -> Self::Output {
        clamp(self, val)
    }
}

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

// todo: Const trait implementations
pub trait NonStandardInteger<T, const BITS: u32, const SIGNED: bool>
where
    T: PartialOrd + Copy,
    Self: Sized,
{
    /// Represents if this integer type is considered to be signed or not.
    const SIGNED: bool = SIGNED;

    /// The size of this integer type in bits.
    const BITS: u32 = BITS;

    /// The smallest value that can be represented by this integer type.
    const MIN: T;

    /// The largest value that can be represented by this integer type.
    const MAX: T;

    /// Convert a `T` into the target without bounds checking
    unsafe fn from_unchecked(n: T) -> Self;

    /// Convert a `T` into the target. Only the `BITS` amount are kept.
    fn from_lossy(n: T) -> Self {
        unsafe { Self::from_unchecked(n).mask() }
    }

    // temporary
    // todo: better names, documentation and usage
    /// Gets a reference to the value of `T`
    fn get_ref(&self) -> T;

    // todo: find better name
    /// Limits the inner value to be between the `MIN` and `MAX`
    fn mask(self) -> Self {
        let clamped = (Self::MIN..Self::MAX).clamp(self.get_ref());
        unsafe { Self::from_unchecked(clamped) }
    }

    /// Returns the smallest value that can be represented by this integer type.
    fn min_value() -> Self {
        unsafe { Self::from_unchecked(Self::MIN) }
    }

    /// Returns the largest value that can be represented by this integer type.
    fn max_value() -> Self {
        unsafe { Self::from_unchecked(Self::MAX) }
    }
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

#[doc(hidden)]
pub macro impl_common($ty:ty) {
    // todo: only implement once instead of for both true/false
    impl<const BITS: u32> const TryFrom<$ty> for int<$ty, BITS>
    where
        Self: NonStandardInteger<$ty, BITS, true>,
    {
        type Error = OutOfRangeIntError;
        fn try_from(data: $ty) -> Result<Self, Self::Error> {
            if data > Self::MAX {
                Err(OutOfRangeIntError)
            } else {
                Ok(Self(data))
            }
        }
    }

    impl<const BITS: u32> const TryFrom<$ty> for int<$ty, BITS>
    where
        Self: NonStandardInteger<$ty, BITS, false>,
    {
        type Error = OutOfRangeIntError;
        fn try_from(data: $ty) -> Result<Self, Self::Error> {
            if data > Self::MAX {
                Err(OutOfRangeIntError)
            } else {
                Ok(Self(data))
            }
        }
    }

    impl<const BITS: u32> const From<int<$ty, BITS>> for $ty {
        #[inline]
        fn from(data: int<$ty, BITS>) -> Self {
            data.0
        }
    }
}

#[doc(hidden)]
pub macro impl_nonstandard_int {
    (unsigned: $ty: ty) => {
        impl<const BITS: u32> const NonStandardInteger<$ty, BITS, false> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS) - 1;
            const MIN: $ty = 0;

            fn get_ref(&self) -> $ty {
                return self.0;
            }

            unsafe fn from_unchecked(n: $ty) -> Self {
                Self(n)
            }
        }

        impl_common!($ty);
    },
    (signed: $ty: ty) => {
        impl<const BITS: u32> const NonStandardInteger<$ty, BITS, true> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS.saturating_sub(1)) - 1;
            const MIN: $ty = !Self::MAX;

            fn get_ref(&self) -> $ty {
                return self.0;
            }

            unsafe fn from_unchecked(n: $ty) -> Self {
                Self(n)
            }
        }

        // impl<const BITS: u32> int<$ty, BITS> {
        //     /// Saturating absolute value. Computes `self.abs()`, returning MAX if `self == MIN` instead of overflowing.
        //     pub const fn saturating_abs(self) -> Self {
        //         if self.0 == Self::MIN {
        //             Self::max_value()
        //         } else {
        //             Self(self.0.saturating_abs())
        //         }
        //     }

        //     /// Saturating integer negation. Computes `-self`, returning `MAX` if `self == MIN` instead of overflowing.
        //     pub const fn saturating_neg(self) -> Self {
        //         if self.0 == Self::MIN {
        //             Self::max_value()
        //         } else {
        //             Self(self.0.saturating_neg())
        //         }
        //     }
        // }

        impl_common!($ty);
    }
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

    mod unsigned {
        use super::*;
        #[allow(non_camel_case_types)]
        type u6 = int<u8, 6>;

        #[test]
        fn max() {
            assert_eq!(u6::MAX, 63);
        }

        #[test]
        fn min() {
            assert_eq!(u6::MIN, 0);
        }

        #[test]
        fn bits() {
            assert_eq!(u6::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(u6::max_value(), int::<u8, 6>(63));
        }

        #[test]
        fn min_value() {
            assert_eq!(u6::min_value(), int::<u8, 6>(0));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value = u6::from_unchecked(u8::MAX);
                let value_u8: u8 = value.into();
                assert_eq!(value_u8, 255);
            }
        }

        #[test]
        fn from_lossy() {
            let value = u6::from_lossy(u8::MAX);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 63);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: u6 = int(15);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 15);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<u6, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(int::<u8, 6>(15)));
            let value: Result<u6, OutOfRangeIntError> = 64.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }

        // mod saturating {
        //     use super::*;

        //     #[test]
        //     fn saturating_add() {
        //         assert_eq!(u6::from_lossy(10).saturating_add(5), u6::from_lossy(15));
        //         assert_eq!(u6::max_value().saturating_add(5), u6::max_value())
        //     }

        //     #[test]
        //     fn saturating_sub() {
        //         assert_eq!(u6::from_lossy(10).saturating_sub(5), u6::from_lossy(5));
        //         assert_eq!(u6::min_value().saturating_sub(5), u6::min_value())
        //     }

        //     #[test]
        //     fn saturating_mul() {
        //         assert_eq!(u6::from_lossy(10).saturating_mul(5), u6::from_lossy(50));
        //         assert_eq!(u6::from_lossy(10).saturating_mul(10), u6::max_value())
        //     }

        //     #[test]
        //     fn saturating_pow() {
        //         assert_eq!(u6::from_lossy(3).saturating_pow(3), u6::from_lossy(27));
        //         assert_eq!(u6::from_lossy(10).saturating_pow(3), u6::max_value())
        //     }
        // }
    }

    mod signed {
        use super::*;
        #[allow(non_camel_case_types)]
        type i6 = int<i8, 6>;

        #[test]
        fn max() {
            assert_eq!(i6::MAX, 31);
        }

        #[test]
        fn min() {
            assert_eq!(i6::MIN, -32);
        }

        #[test]
        fn bits() {
            assert_eq!(i6::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(i6::max_value(), int::<i8, 6>(31));
        }

        #[test]
        fn min_value() {
            assert_eq!(i6::min_value(), int::<i8, 6>(-32));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value = i6::from_unchecked(i8::MAX);
                let value_i8: i8 = value.into();
                assert_eq!(value_i8, 127);
            }
        }

        #[test]
        fn from_lossy() {
            assert_eq!(i6::from_lossy(12).0, 12);
            assert_eq!(i6::from_lossy(-12).0, -12);
            assert_eq!(i6::from_lossy(i8::MAX).0, 31);
            assert_eq!(i6::from_lossy(i8::MIN).0, -32);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: i6 = int(15);
            let value_i8: i8 = value.into();
            assert_eq!(value_i8, 15);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<i6, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(int::<i8, 6>(15)));
            let value: Result<i6, OutOfRangeIntError> = 32.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }

        // mod saturating {
        //     use super::*;

        //     #[test]
        //     fn saturating_add() {
        //         assert_eq!(i6::from_lossy(10).saturating_add(5), i6::from_lossy(15));
        //         assert_eq!(i6::max_value().saturating_add(5), i6::max_value())
        //     }

        //     #[test]
        //     fn saturating_sub() {
        //         assert_eq!(i6::from_lossy(10).saturating_sub(5), i6::from_lossy(5));
        //         assert_eq!(i6::min_value().saturating_sub(5), i6::min_value())
        //     }

        //     #[test]
        //     fn saturating_mul() {
        //         assert_eq!(i6::from_lossy(10).saturating_mul(2), i6::from_lossy(20));
        //         assert_eq!(i6::from_lossy(10).saturating_mul(10), i6::max_value())
        //     }

        //     #[test]
        //     fn saturating_pow() {
        //         assert_eq!(i6::from_lossy(3).saturating_pow(3), i6::from_lossy(27));
        //         assert_eq!(i6::from_lossy(10).saturating_pow(5), i6::max_value())
        //     }

        //     #[test]
        //     fn saturating_neg() {
        //         assert_eq!(i6::from_lossy(3).saturating_neg(), i6::from_lossy(-3));
        //         assert_eq!(i6::from_lossy(-3).saturating_neg(), i6::from_lossy(3));
        //         assert_eq!(i6::max_value().saturating_neg(), i6::from_lossy(-31));
        //         assert_eq!(i6::min_value().saturating_neg(), i6::max_value());
        //     }

        //     #[test]
        //     fn saturating_abs() {
        //         assert_eq!(i6::from_lossy(3).saturating_abs(), i6::from_lossy(3));
        //         assert_eq!(i6::from_lossy(-3).saturating_abs(), i6::from_lossy(3));
        //         assert_eq!(i6::max_value().saturating_abs(), i6::max_value());
        //         assert_eq!(i6::min_value().saturating_abs(), i6::max_value());
        //     }
        // }
    }
}
