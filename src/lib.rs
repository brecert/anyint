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

pub mod clamp;
pub mod convert;
pub mod ops;

// todo: no std
// todo: unstable feature flags
use crate::clamp::{Clamp, Wrap};
use crate::convert::{LossyFrom, UncheckedFrom, WrappingFrom};
use std::convert::{From, TryFrom};
use std::fmt::{self, Display};
use thiserror::Error;

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

// todo: const trait implementations
// todo: maybe default implementations should not require `Self` traits
pub trait NonStandardInteger<T, const BITS: u32, const SIGNED: bool>
where
    T: PartialOrd + Copy,
    Self: LossyFrom<T> + UncheckedFrom<T> + AsRef<T>,
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

    // todo: find better name
    /// Limits the inner value to be between `MIN` and `MAX`
    fn clamp(self) -> Self {
        let clamped = (Self::MIN..Self::MAX).clamp(*self.as_ref());
        // SAFETY: the value has already been clamped to be in the valid range of `int`
        unsafe { Self::from_unchecked(clamped) }
    }
    /// Returns the smallest value that can be represented by this integer type.
    fn min_value() -> Self {
        // SAFETY: The user ensures that `MIN` is valid
        unsafe { Self::from_unchecked(Self::MIN) }
    }
    /// Returns the largest value that can be represented by this integer type.
    fn max_value() -> Self {
        // SAFETY: The user ensures that `MAX` is valid
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
    // SAFETY: `from_unchecked` is clamped, making it a valid value
    unsafe { I::from_unchecked(n).clamp() }
}

/// Provides integer methods.
pub trait NonStandardIntegerExt<T: PartialOrd + Copy, const BITS: u32, const SIGNED: bool>:
    NonStandardInteger<T, BITS, SIGNED>
{
    /// Checked integer addition. Computes `self + rhs`, returning `None`
    /// if overflow occurred.
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs`, returning `None`
    /// if overflow occurred.
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
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

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the
    /// boundary of the type.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the
    /// boundary of the type.
    fn wrapping_sub(self, rhs: Self) -> Self;

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at
    /// the boundary of the type.
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the
    /// boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one divides `MIN / -1` on a signed type (where
    /// `MIN` is the negative minimal value for the type); this is equivalent to `-MIN`, a positive value
    /// that is too large to represent in the type. In such a case, this function returns `MIN` itself.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn wrapping_div(self, rhs: Self) -> Self;

    // fn wrapping_rem(self, rhs: Self) -> Self;
    // fn wrapping_shl(self, rhs: Self) -> Self;
    // fn wrapping_shr(self, rhs: Self) -> Self;
    // fn wrapping_pow(self, exp: u32) -> Self;

    /// Calculates `self` + `rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would
    /// occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_add(self, rhs: Self) -> (Self, bool);

    /// Calculates `self` - `rhs`
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic overflow
    /// would occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic overflow
    /// would occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would
    /// occur. If an overflow would occur then self is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn overflowing_div(self, rhs: Self) -> (Self, bool);

    // fn overflowing_rem(self, rhs: Self) -> Self;
    // fn overflowing_shl(self, rhs: Self) -> Self;
    // fn overflowing_shr(self, rhs: Self) -> Self;
    // fn overflowing_pow(self, exp: u32) -> Self;
}

/// Provides integer methods that only make sense with signed integers.
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

impl<T, const BITS: u32> const AsRef<T> for int<T, BITS> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

// todo: Determine if this fits or not
impl<T, const BITS: u32> int<T, BITS>
where
    Self: LossyFrom<T>,
{
    /// Convenience wrapper around `from_lossy`.
    pub fn new(n: T) -> Self {
        Self::from_lossy(n)
    }
}

#[doc(hidden)]
pub macro fn_checked($($name:ident,)*) {
    $(
        fn $name(self, rhs: Self) -> Option<Self> {
            match self.as_ref().$name(*rhs.as_ref()) {
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
            from_lossy(self.as_ref().$name(*rhs.as_ref()))
        }
    )*
}

#[doc(hidden)]
pub macro fn_wrapping($($fn_name:ident => $wrap_name:ident,)*) {
    $(
        fn $fn_name(self, rhs: Self) -> Self {
            self.$wrap_name(rhs).0
        }
    )*
}

#[doc(hidden)]
pub macro impl_common($ty:ty, $signed:literal) {
    impl<const BITS: u32> const WrappingFrom<$ty> for int<$ty, BITS> {
        /// Convert a `T` into the target. Only the `BITS` amount are kept.
        fn from_wrapping(val: $ty) -> Self {
            // SAFETY: `from_unchecked` is wrapped, making it a valid value
            unsafe { Self::from_unchecked(val).wrap() }
        }
    }

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

    /// ```
    /// use anyint::*;
    /// use anyint::convert::*;
    #[doc = concat!("let x = int::<", stringify!($ty), ", { ", stringify!(6), " }>::from_lossy(10);")]
    /// assert_eq!(x.as_ref(), &10);
    /// ```
    impl<const BITS: u32> const NonStandardIntegerExt<$ty, BITS, $signed> for int<$ty, BITS> {
        // checked implementations are not based on overflowing implementations because they can be implemented independently a little more performant.
        // todo: check performance...
        fn_checked!(
            checked_add,
            checked_sub,
            checked_mul,
            checked_div,
            checked_rem,
        );

        fn_saturating!(saturating_add, saturating_sub, saturating_mul,);

        fn saturating_pow(self, rhs: u32) -> Self {
            from_lossy(self.as_ref().saturating_pow(rhs))
        }

        fn_wrapping!(
            wrapping_add => overflowing_add,
            wrapping_sub => overflowing_sub,
            wrapping_mul => overflowing_mul,
            wrapping_div => overflowing_div,
        );

        // fn wrapping_add(self, rhs: Self) -> Self {
        //     self.overflowing_add(rhs).0
        // }

        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::max_value().overflowing_add(N6::from_lossy(1)), (N6::min_value(), true));
        /// assert_eq!(N6::min_value().overflowing_add(N6::from_lossy(1)), (N6::from_lossy(N6::MIN + 1), false));
        /// ```
        fn overflowing_add(self, rhs: Self) -> (Self, bool) {
            Self(*self.as_ref() + *rhs.as_ref()).wrapped()
        }

        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::min_value().overflowing_sub(N6::from_lossy(1)), (N6::max_value(), true));
        /// assert_eq!(N6::max_value().overflowing_sub(N6::from_lossy(1)), (N6::from_lossy(N6::MAX - 1), false));
        /// ```
        fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
            let a = *self.as_ref();
            let b = *rhs.as_ref();

            if a >= b {
                (Self(a - b), false)
            } else {
                (Self((1 << Self::BITS) - (b - a)).wrap(), true)
            }
        }

        fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
            Self(self.as_ref().wrapping_mul(*rhs.as_ref())).wrapped()
        }

        // todo: specialize for unsigned so that optimized normal division
        fn overflowing_div(self, rhs: Self) -> (Self, bool) {
            Self(*self.as_ref() / *rhs.as_ref()).wrapped()
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
            *data.as_ref()
        }
    }
}

#[doc(hidden)]
pub macro impl_nonstandard_int {
    (unsigned: $ty: ty) => {
        impl<const BITS: u32> const Wrap<Self> for int<$ty, BITS> {
            #[inline]
            fn wrapped(self) -> (Self, bool) {
                let wrapped = self.0 & Self::MAX;
                (Self(wrapped), self.0 != wrapped)
            }

            #[inline]
            fn wrap(self) -> Self {
                self.wrapped().0
            }
        }

        impl<const BITS: u32> const NonStandardInteger<$ty, BITS, false> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS) - 1;
            const MIN: $ty = 0;
        }

        impl_common!($ty, false);
    },
    (signed: $ty: ty) => {
        impl<const BITS: u32> const Wrap<Self> for int<$ty, BITS> {
            #[inline]
            fn wrapped(self) -> (Self, bool) {
                let offset = <$ty>::BITS - Self::BITS;
                let wrapped = (self.0 << offset) >> offset;
                (Self(wrapped), self.0 != wrapped)
            }

            #[inline]
            fn wrap(self) -> Self {
                self.wrapped().0
            }
        }

        impl<const BITS: u32> const NonStandardInteger<$ty, BITS, true> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS.saturating_sub(1)) - 1;
            const MIN: $ty = !Self::MAX;
        }

        impl<const BITS: u32> const NonStandardIntegerSigned<$ty, BITS> for int<$ty, BITS> {
            fn saturating_abs(self) -> Self {
                if *self.as_ref() == Self::MIN {
                    Self(Self::MAX)
                } else {
                    Self(self.as_ref().saturating_abs())
                }
            }

            fn saturating_neg(self) -> Self {
                if *self.as_ref() == Self::MIN {
                    Self(Self::MAX)
                } else {
                    Self(self.as_ref().saturating_neg())
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

#[cfg(doctest)]
mod doctest {
    use super::*;

    /// ```compile_fail
    /// use anyint::*;
    /// let x = anyint::int::<i8, 8>::MAX;
    /// ```
    pub struct SIntOnlyTakesValidSize;

    /// ```compile_fail
    /// use anyint::*;
    /// let x = anyint::int::<u8, 8>::MAX;
    /// ```
    pub struct UIntOnlyTakesValidSize;

    /// ```
    /// use anyint::*;
    /// let x = int::<u8, 7>::MAX;
    /// let x = int::<i8, 7>::MAX;
    /// ```
    pub struct IntTakesValidSizes;
}

#[cfg(test)]
mod test {
    use super::*;
    use convert::LossyInto;
    use std::convert::TryInto;

    #[test]
    fn type_inference() {
        let _: int<u8, 6> = int::from_lossy(5);
        let _: int<i32, 15> = int::from_lossy(5);
    }

    #[test]
    fn from_wrapping() {
        let x: int<u8, 6> = int::from_wrapping(65);
        assert_eq!(x.as_ref(), &1);
    }

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
            let value = u6::new(u8::MAX);
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
                    u6::new(10).checked_add(5.into_lossy()),
                    Some(u6::new(15))
                );
                assert_eq!(u6::max_value().checked_add(5.into_lossy()), None)
            }

            #[test]
            fn checked_sub() {
                assert_eq!(
                    u6::new(10).checked_sub(5.into_lossy()),
                    Some(u6::new(5))
                );
                assert_eq!(u6::min_value().checked_sub(5.into_lossy()), None)
            }

            #[test]
            fn checked_mul() {
                assert_eq!(
                    u6::new(10).checked_mul(5.into_lossy()),
                    Some(u6::new(50))
                );
                assert_eq!(u6::new(10).checked_mul(10.into_lossy()), None)
            }

            #[test]
            fn checked_div() {
                assert_eq!(
                    u6::new(10).checked_div(5.into_lossy()),
                    Some(u6::new(2))
                );
                assert_eq!(u6::new(10).checked_div(0.into_lossy()), None)
            }

            #[test]
            fn checked_rem() {
                assert_eq!(
                    u6::new(8).checked_rem(3.into_lossy()),
                    Some(u6::new(2))
                );
                assert_eq!(u6::new(10).checked_rem(0.into_lossy()), None)
            }
        }

        mod saturating {
            use super::*;

            #[test]
            fn saturating_add() {
                assert_eq!(
                    u6::new(10).saturating_add(5.into_lossy()),
                    u6::new(15)
                );
                assert_eq!(
                    u6::max_value().saturating_add(5.into_lossy()),
                    u6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(
                    u6::new(10).saturating_sub(5.into_lossy()),
                    u6::new(5)
                );
                assert_eq!(
                    u6::min_value().saturating_sub(5.into_lossy()),
                    u6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(
                    u6::new(10).saturating_mul(5.into_lossy()),
                    u6::new(50)
                );
                assert_eq!(
                    u6::new(10).saturating_mul(10.into_lossy()),
                    u6::max_value()
                )
            }

            #[test]
            fn saturating_pow() {
                assert_eq!(u6::new(3).saturating_pow(3), u6::new(27));
                assert_eq!(u6::new(10).saturating_pow(3), u6::max_value())
            }
        }

        mod wrapping {
            use super::*;

            #[test]
            fn wrapping_add() {
                assert_eq!(
                    u6::new(5).wrapping_add(2.into_lossy()),
                    u6::new(7)
                );
                assert_eq!(
                    u6::new(u6::MAX).wrapping_add(2.into_lossy()),
                    u6::new(u6::MIN + 1)
                );
            }

            #[test]
            fn wrapping_sub() {
                assert_eq!(
                    u6::new(5).wrapping_sub(2.into_lossy()),
                    u6::new(3)
                );
                assert_eq!(
                    u6::new(u6::MIN).wrapping_sub(1.into_lossy()),
                    u6::new(u6::MAX)
                );
                assert_eq!(
                    u6::new(u6::MIN).wrapping_sub(20.into_lossy()),
                    u6::new(u6::MAX - 19)
                );
                assert_eq!(
                    u6::new(32).wrapping_sub(32.into_lossy()),
                    u6::new(0)
                );
                assert_eq!(
                    u6::new(32).wrapping_sub(33.into_lossy()),
                    u6::new(u6::MAX)
                );
                assert_eq!(
                    u6::new(0).wrapping_sub(10.into_lossy()),
                    u6::new(u6::MAX - 9)
                );
            }

            #[test]
            fn wrapping_mul() {
                assert_eq!(
                    u6::new(5).wrapping_mul(2.into_lossy()),
                    u6::new(10)
                );
                assert_eq!(
                    u6::new(32).wrapping_mul(2.into_lossy()),
                    u6::new(0)
                );
                assert_eq!(
                    u6::new(10).wrapping_mul(10.into_lossy()),
                    u6::new(36)
                );
            }

            #[test]
            fn wrapping_div() {
                assert_eq!(
                    u6::new(6).wrapping_div(2.into_lossy()),
                    u6::new(3)
                );
                assert_eq!(
                    u6::new(10).wrapping_div(3.into_lossy()),
                    u6::new(3)
                );
                assert_eq!(
                    u6::new(0).wrapping_div(3.into_lossy()),
                    u6::new(0)
                );
            }

            #[test]
            #[should_panic]
            fn wrapping_div_with_zero() {
                u6::new(3).wrapping_div(0.into_lossy());
            }
        }

        mod overflowing {
            use super::*;

            #[test]
            fn overflowing_add() {
                assert_eq!(
                    u6::new(5).overflowing_add(2.into_lossy()),
                    (u6::new(7), false)
                );
                assert_eq!(
                    u6::new(u6::MAX).overflowing_add(2.into_lossy()),
                    (u6::new(u6::MIN + 1), true)
                );
            }

            #[test]
            fn overflowing_sub() {
                assert_eq!(
                    u6::new(5).overflowing_sub(2.into_lossy()),
                    (u6::new(3), false)
                );
                assert_eq!(
                    u6::new(u6::MIN).overflowing_sub(1.into_lossy()),
                    (u6::new(u6::MAX), true)
                );
                assert_eq!(
                    u6::new(u6::MIN).overflowing_sub(20.into_lossy()),
                    (u6::new(u6::MAX - 19), true)
                );
                assert_eq!(
                    u6::new(32).overflowing_sub(32.into_lossy()),
                    (u6::new(0), false)
                );
                assert_eq!(
                    u6::new(32).overflowing_sub(33.into_lossy()),
                    (u6::new(u6::MAX), true)
                );
                assert_eq!(
                    u6::new(0).overflowing_sub(10.into_lossy()),
                    (u6::new(u6::MAX - 9), true)
                );
            }

            #[test]
            fn overflowing_mul() {
                assert_eq!(
                    u6::new(5).overflowing_mul(2.into_lossy()),
                    (u6::new(10), false)
                );
                assert_eq!(
                    u6::new(32).overflowing_mul(2.into_lossy()),
                    (u6::new(0), true)
                );
                assert_eq!(
                    u6::new(10).overflowing_mul(10.into_lossy()),
                    (u6::new(36), true)
                );
            }

            #[test]
            fn overflowing_div() {
                assert_eq!(
                    u6::new(6).overflowing_div(2.into_lossy()),
                    (u6::new(3), false)
                );
                assert_eq!(
                    u6::new(10).overflowing_div(3.into_lossy()),
                    (u6::new(3), false)
                );
                assert_eq!(
                    u6::new(0).overflowing_div(3.into_lossy()),
                    (u6::new(0), false)
                );
            }

            #[test]
            #[should_panic]
            fn overflowing_div_with_zero() {
                u6::new(3).overflowing_div(0.into_lossy());
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
                    i6::new(10).saturating_add(5.into_lossy()),
                    i6::new(15)
                );
                assert_eq!(
                    i6::max_value().saturating_add(5.into_lossy()),
                    i6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(
                    i6::new(10).saturating_sub(5.into_lossy()),
                    i6::new(5)
                );
                assert_eq!(
                    i6::min_value().saturating_sub(5.into_lossy()),
                    i6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(
                    i6::new(10).saturating_mul(2.into_lossy()),
                    i6::new(20)
                );
                assert_eq!(
                    i6::new(10).saturating_mul(10.into_lossy()),
                    i6::max_value()
                )
            }

            #[test]
            fn saturating_pow() {
                assert_eq!(i6::new(3).saturating_pow(3), i6::new(27));
                assert_eq!(i6::new(10).saturating_pow(5), i6::max_value())
            }

            #[test]
            fn saturating_neg() {
                assert_eq!(i6::new(3).saturating_neg(), i6::new(-3));
                assert_eq!(i6::new(-3).saturating_neg(), i6::new(3));
                assert_eq!(i6::max_value().saturating_neg(), i6::new(-31));
                assert_eq!(i6::min_value().saturating_neg(), i6::max_value());
            }

            #[test]
            fn saturating_abs() {
                assert_eq!(i6::new(3).saturating_abs(), i6::new(3));
                assert_eq!(i6::new(-3).saturating_abs(), i6::new(3));
                assert_eq!(i6::max_value().saturating_abs(), i6::max_value());
                assert_eq!(i6::min_value().saturating_abs(), i6::max_value());
            }
        }

        mod overflowing {
            use super::*;

            #[test]
            fn overflowing_add() {
                assert_eq!(
                    i6::new(5).overflowing_add(2.into_lossy()),
                    (i6::new(7), false)
                );
                assert_eq!(
                    i6::new(i6::MAX).overflowing_add(2.into_lossy()),
                    (i6::new(i6::MIN + 1), true)
                );
            }

            #[test]
            fn overflowing_sub() {
                assert_eq!(
                    i6::new(5).overflowing_sub(2.into_lossy()),
                    (i6::new(3), false)
                );
                assert_eq!(
                    i6::new(i6::MIN).overflowing_sub(1.into_lossy()),
                    (i6::new(i6::MAX), true)
                );
                assert_eq!(
                    i6::new(i6::MIN).overflowing_sub(20.into_lossy()),
                    (i6::new(i6::MAX - 19), true)
                );
                assert_eq!(
                    i6::new(32).overflowing_sub(32.into_lossy()),
                    (i6::new(0), false)
                );
                assert_eq!(
                    i6::new(i6::MAX - 2).overflowing_sub((i6::MAX - 1).into_lossy()),
                    (i6::new(-1), true)
                );
                assert_eq!(
                    i6::new(i6::MIN).overflowing_sub(10.into_lossy()),
                    (i6::new(i6::MAX - 9), true)
                );
            }

            #[test]
            fn overflowing_mul() {
                assert_eq!(
                    i6::new(5).overflowing_mul(2.into_lossy()),
                    (i6::new(10), false)
                );
                assert_eq!(
                    i6::new(16).overflowing_mul(4.into_lossy()),
                    (i6::new(0), true)
                );
                assert_eq!(
                    i6::new(30).overflowing_mul(30.into_lossy()),
                    (i6::new(4), true)
                );
            }

            #[test]
            fn overflowing_div() {
                assert_eq!(
                    i6::new(6).overflowing_div(2.into_lossy()),
                    (i6::new(3), false)
                );
                assert_eq!(
                    i6::new(10).overflowing_div(3.into_lossy()),
                    (i6::new(3), false)
                );
                assert_eq!(
                    i6::new(0).overflowing_div(3.into_lossy()),
                    (i6::new(0), false)
                );
            }

            #[test]
            #[should_panic]
            fn overflowing_div_with_zero() {
                i6::new(3).overflowing_div(0.into_lossy());
            }
        }
    }
}
