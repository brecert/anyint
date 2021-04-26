#![allow(incomplete_features)]
#![feature(
    decl_macro,
    const_fn,
    const_trait_impl,
    const_refs_to_cell,
    associated_type_defaults,
    specialization
)]

pub mod clamp;
pub mod convert;

// todo: no std
// todo: unstable feature flags
use crate::clamp::Clamp;
use crate::convert::{LossyFrom, UncheckedFrom};
use std::convert::{From, TryFrom};
use std::fmt::{self, Display};
use thiserror::Error;

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

// todo: Const trait implementations
pub trait NonStandardInteger<T, const BITS: u32, const SIGNED: bool>
where
    T: PartialOrd + Copy,
    Self: LossyFrom<T> + UncheckedFrom<T>,
{
    // TODO: find a better name for this.
    /// The underlying representation of the integer.
    type Repr = T;

    /// Represents if this integer type is considered to be signed or not.
    const SIGNED: bool = SIGNED;

    /// The size of this integer type in bits.
    const BITS: u32 = BITS;

    /// The smallest value that can be represented by this integer type.
    const MIN: T;

    /// The largest value that can be represented by this integer type.
    const MAX: T;

    /// Convert a `T` into the target without bounds checking

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

#[inline(always)]
#[doc(hidden)]
pub const fn from_lossy<
    I: NonStandardInteger<T, BITS, SIGNED> + UncheckedFrom<T>,
    T: PartialOrd + Copy,
    const BITS: u32,
    const SIGNED: bool,
>(
    n: T,
) -> I {
    unsafe { I::from_unchecked(n).mask() }
}

pub trait NonStandardIntegerExt<T: PartialOrd + Copy, const BITS: u32, const SIGNED: bool>:
    NonStandardInteger<T, BITS, SIGNED>
{
    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred.
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occurred.
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0`.
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0`.
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    // fn checked_shl(self, rhs: Self) -> Option<Self>;
    // fn checked_shr(self, rhs: Self) -> Option<Self>;
    // fn checked_pow(self, rhs: u32) -> Self;

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(self, rhs: Self) -> Self;

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(self, rhs: Self) -> Self;

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_mul(self, rhs: Self) -> Self;

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric bounds instead of overflowing.
    fn saturating_pow(self, exp: u32) -> Self;

    // fn wrapping_add(self, exp: Self) -> Self;
    // fn wrapping_sub(self, exp: Self) -> Self;
    // fn wrapping_mul(self, exp: Self) -> Self;
    // fn wrapping_div(self, exp: Self) -> Self;
    // fn wrapping_rem(self, exp: Self) -> Self;
    // fn wrapping_shl(self, exp: Self) -> Self;
    // fn wrapping_shr(self, exp: Self) -> Self;
    // fn wrapping_pow(self, exp: u32) -> Self;
    // fn overflowing_add(self, exp: Self) -> Self;
    // fn overflowing_sub(self, exp: Self) -> Self;
    // fn overflowing_mul(self, exp: Self) -> Self;
    // fn overflowing_div(self, exp: Self) -> Self;
    // fn overflowing_rem(self, exp: Self) -> Self;
    // fn overflowing_shl(self, exp: Self) -> Self;
    // fn overflowing_shr(self, exp: Self) -> Self;
    // fn overflowing_pow(self, exp: u32) -> Self;
}

pub trait NonStandardIntegerSigned<T: PartialOrd + Copy, const BITS: u32>:
    NonStandardInteger<T, BITS, true>
{
    /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if `self == MIN` instead of overflowing.
    fn saturating_abs(self) -> Self;

    /// Saturating integer negation. Computes `-self`, returning `MAX` if `self == MIN` instead of overflowing.
    fn saturating_neg(self) -> Self;
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
pub macro fn_checked($($name:ident,)*) {
    $(
        fn $name(self, rhs: Self) -> Option<Self> {
            match self.get_ref().$name(rhs.get_ref()) {
                Some(val) if val <= Self::MAX => Some(Self(val)),
                _ => None
            }
        }
    )*
}

#[doc(hidden)]
pub macro fn_saturating($($name:ident,)*) {
    $(
        fn $name(self, rhs: Self) -> Self {
            from_lossy(self.get_ref().$name(rhs.get_ref()))
        }
    )*
}

#[doc(hidden)]
pub macro impl_common($ty:ty, $signed:literal) {
    impl<const BITS: u32> const LossyFrom<$ty> for int<$ty, BITS> {
        /// Convert a `T` into the target. Only the `BITS` amount are kept.
        fn from_lossy(val: $ty) -> Self {
            from_lossy(val)
        }
    }

    /// Convert a `T` into the target without bounds checking
    unsafe impl<const BITS: u32> const UncheckedFrom<$ty> for int<$ty, BITS> {
        unsafe fn from_unchecked(n: $ty) -> Self {
            Self(n)
        }
    }

    impl<const BITS: u32> const NonStandardIntegerExt<$ty, BITS, $signed> for int<$ty, BITS> {
        fn_checked!(
            checked_add,
            checked_sub,
            checked_mul,
            checked_div,
            checked_rem,
        );

        fn_saturating!(saturating_add, saturating_sub, saturating_mul,);

        fn saturating_pow(self, rhs: u32) -> Self {
            from_lossy(self.get_ref().saturating_pow(rhs))
        }
    }

    impl<const BITS: u32> const TryFrom<$ty> for int<$ty, BITS>
    where
        Self: NonStandardInteger<$ty, BITS, $signed>,
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
            data.get_ref()
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
        }

        impl_common!($ty, false);
    },
    (signed: $ty: ty) => {
        impl<const BITS: u32> const NonStandardInteger<$ty, BITS, true> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS.saturating_sub(1)) - 1;
            const MIN: $ty = !Self::MAX;

            fn get_ref(&self) -> $ty {
                return self.0;
            }
        }

        impl<const BITS: u32> const NonStandardIntegerSigned<$ty, BITS> for int<$ty, BITS> {
            fn saturating_abs(self) -> Self {
                if self.get_ref() == Self::MIN {
                    Self(Self::MAX)
                } else {
                    Self(self.get_ref().saturating_abs())
                }
            }

            fn saturating_neg(self) -> Self {
                if self.get_ref() == Self::MIN {
                    Self(Self::MAX)
                } else {
                    Self(self.get_ref().saturating_neg())
                }
            }
        }

        impl_common!($ty, true);
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
    use convert::LossyInto;
    use std::convert::TryInto;

    // #[test]
    // #[ignore = "not yet implemented due to rust's current type system"]
    // fn test_invalid_bits_size() {
    //     let _ = int::<u8, 8>::MAX;
    // }

    mod unsigned_common {
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

        mod checked {
            use super::*;

            #[test]
            fn checked_add() {
                assert_eq!(
                    u6::from_lossy(10).checked_add(5.into_lossy()),
                    Some(u6::from_lossy(15))
                );
                assert_eq!(u6::max_value().checked_add(5.into_lossy()), None)
            }

            #[test]
            fn checked_sub() {
                assert_eq!(
                    u6::from_lossy(10).checked_sub(5.into_lossy()),
                    Some(u6::from_lossy(5))
                );
                assert_eq!(u6::min_value().checked_sub(5.into_lossy()), None)
            }

            #[test]
            fn checked_mul() {
                assert_eq!(
                    u6::from_lossy(10).checked_mul(5.into_lossy()),
                    Some(u6::from_lossy(50))
                );
                assert_eq!(u6::from_lossy(10).checked_mul(10.into_lossy()), None)
            }

            #[test]
            fn checked_div() {
                assert_eq!(
                    u6::from_lossy(10).checked_div(5.into_lossy()),
                    Some(u6::from_lossy(2))
                );
                assert_eq!(u6::from_lossy(10).checked_div(0.into_lossy()), None)
            }

            #[test]
            fn checked_rem() {
                assert_eq!(
                    u6::from_lossy(8).checked_rem(3.into_lossy()),
                    Some(u6::from_lossy(2))
                );
                assert_eq!(u6::from_lossy(10).checked_rem(0.into_lossy()), None)
            }
        }

        mod saturating {
            use super::*;

            #[test]
            fn saturating_add() {
                assert_eq!(
                    u6::from_lossy(10).saturating_add(5.into_lossy()),
                    u6::from_lossy(15)
                );
                assert_eq!(
                    u6::max_value().saturating_add(5.into_lossy()),
                    u6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(
                    u6::from_lossy(10).saturating_sub(5.into_lossy()),
                    u6::from_lossy(5)
                );
                assert_eq!(
                    u6::min_value().saturating_sub(5.into_lossy()),
                    u6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(
                    u6::from_lossy(10).saturating_mul(5.into_lossy()),
                    u6::from_lossy(50)
                );
                assert_eq!(
                    u6::from_lossy(10).saturating_mul(10.into_lossy()),
                    u6::max_value()
                )
            }

            #[test]
            fn saturating_pow() {
                assert_eq!(u6::from_lossy(3).saturating_pow(3), u6::from_lossy(27));
                assert_eq!(u6::from_lossy(10).saturating_pow(3), u6::max_value())
            }
        }
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

        mod saturating {
            use super::*;

            #[test]
            fn saturating_add() {
                assert_eq!(
                    i6::from_lossy(10).saturating_add(5.into_lossy()),
                    i6::from_lossy(15)
                );
                assert_eq!(
                    i6::max_value().saturating_add(5.into_lossy()),
                    i6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(
                    i6::from_lossy(10).saturating_sub(5.into_lossy()),
                    i6::from_lossy(5)
                );
                assert_eq!(
                    i6::min_value().saturating_sub(5.into_lossy()),
                    i6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(
                    i6::from_lossy(10).saturating_mul(2.into_lossy()),
                    i6::from_lossy(20)
                );
                assert_eq!(
                    i6::from_lossy(10).saturating_mul(10.into_lossy()),
                    i6::max_value()
                )
            }

            #[test]
            fn saturating_pow() {
                assert_eq!(i6::from_lossy(3).saturating_pow(3), i6::from_lossy(27));
                assert_eq!(i6::from_lossy(10).saturating_pow(5), i6::max_value())
            }

            #[test]
            fn saturating_neg() {
                assert_eq!(i6::from_lossy(3).saturating_neg(), i6::from_lossy(-3));
                assert_eq!(i6::from_lossy(-3).saturating_neg(), i6::from_lossy(3));
                assert_eq!(i6::max_value().saturating_neg(), i6::from_lossy(-31));
                assert_eq!(i6::min_value().saturating_neg(), i6::max_value());
            }

            #[test]
            fn saturating_abs() {
                assert_eq!(i6::from_lossy(3).saturating_abs(), i6::from_lossy(3));
                assert_eq!(i6::from_lossy(-3).saturating_abs(), i6::from_lossy(3));
                assert_eq!(i6::max_value().saturating_abs(), i6::max_value());
                assert_eq!(i6::min_value().saturating_abs(), i6::max_value());
            }
        }
    }
}
