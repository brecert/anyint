use crate::clamp::Wrap;
use crate::convert::{LossyFrom, UncheckedFrom, WrappingFrom};
use crate::non_standard_integer::{
    NonStandardInteger, NonStandardIntegerCommon, NonStandardIntegerSigned,
};
use std::convert::{From, TryFrom};
use std::fmt::{self, Display};
use thiserror::Error;

/// The error type returned when a checked `int` conversion fails.
#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

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
            Self::from_lossy(self.as_ref().$name(*rhs.as_ref()))
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
    impl<const BITS: u32> const NonStandardIntegerCommon<$ty, BITS, $signed> for int<$ty, BITS> {
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
            Self::from_lossy(self.as_ref().saturating_pow(rhs))
        }

        fn_wrapping!(
            wrapping_add => overflowing_add,
            wrapping_sub => overflowing_sub,
            wrapping_mul => overflowing_mul,
            wrapping_div => overflowing_div,
        );
    
        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(1).wrapping_shl(4), N6::new(16));
        /// assert_eq!(N6::new(1).wrapping_shl(128), N6::new(1));
        /// ```
        fn wrapping_shl(self, rhs: u32) -> Self {
            Self(self.as_ref().wrapping_shl(rhs & (Self::BITS - 1)))
        }

        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(16).wrapping_shr(4), N6::new(1));
        /// assert_eq!(N6::new(16).wrapping_shr(128), N6::new(16));
        /// ```
        fn wrapping_shr(self, rhs: u32) -> Self {
            Self(self.as_ref().wrapping_shr(rhs & (Self::BITS - 1)))
        }

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
    
        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(1).overflowing_shl(4), (N6::new(16), false));
        /// assert_eq!(N6::new(1).overflowing_shl(128), (N6::new(1), true));
        /// ```
        fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shl(rhs), (rhs > (Self::BITS - 1)))
        }

        /// ```
        /// use anyint::*;
        /// use anyint::convert::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(16).overflowing_shr(4), (N6::new(1), false));
        /// assert_eq!(N6::new(16).overflowing_shr(128), (N6::new(16), true));
        /// ```
        fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shr(rhs), (rhs > (Self::BITS - 1)))
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
    use crate::convert::LossyInto;
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
                assert_eq!(u6::new(10).checked_add(5.into_lossy()), Some(u6::new(15)));
                assert_eq!(u6::max_value().checked_add(5.into_lossy()), None)
            }

            #[test]
            fn checked_sub() {
                assert_eq!(u6::new(10).checked_sub(5.into_lossy()), Some(u6::new(5)));
                assert_eq!(u6::min_value().checked_sub(5.into_lossy()), None)
            }

            #[test]
            fn checked_mul() {
                assert_eq!(u6::new(10).checked_mul(5.into_lossy()), Some(u6::new(50)));
                assert_eq!(u6::new(10).checked_mul(10.into_lossy()), None)
            }

            #[test]
            fn checked_div() {
                assert_eq!(u6::new(10).checked_div(5.into_lossy()), Some(u6::new(2)));
                assert_eq!(u6::new(10).checked_div(0.into_lossy()), None)
            }

            #[test]
            fn checked_rem() {
                assert_eq!(u6::new(8).checked_rem(3.into_lossy()), Some(u6::new(2)));
                assert_eq!(u6::new(10).checked_rem(0.into_lossy()), None)
            }
        }

        mod saturating {
            use super::*;

            #[test]
            fn saturating_add() {
                assert_eq!(u6::new(10).saturating_add(5.into_lossy()), u6::new(15));
                assert_eq!(
                    u6::max_value().saturating_add(5.into_lossy()),
                    u6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(u6::new(10).saturating_sub(5.into_lossy()), u6::new(5));
                assert_eq!(
                    u6::min_value().saturating_sub(5.into_lossy()),
                    u6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(u6::new(10).saturating_mul(5.into_lossy()), u6::new(50));
                assert_eq!(u6::new(10).saturating_mul(10.into_lossy()), u6::max_value())
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
                assert_eq!(u6::new(5).wrapping_add(2.into_lossy()), u6::new(7));
                assert_eq!(
                    u6::new(u6::MAX).wrapping_add(2.into_lossy()),
                    u6::new(u6::MIN + 1)
                );
            }

            #[test]
            fn wrapping_sub() {
                assert_eq!(u6::new(5).wrapping_sub(2.into_lossy()), u6::new(3));
                assert_eq!(
                    u6::new(u6::MIN).wrapping_sub(1.into_lossy()),
                    u6::new(u6::MAX)
                );
                assert_eq!(
                    u6::new(u6::MIN).wrapping_sub(20.into_lossy()),
                    u6::new(u6::MAX - 19)
                );
                assert_eq!(u6::new(32).wrapping_sub(32.into_lossy()), u6::new(0));
                assert_eq!(u6::new(32).wrapping_sub(33.into_lossy()), u6::new(u6::MAX));
                assert_eq!(
                    u6::new(0).wrapping_sub(10.into_lossy()),
                    u6::new(u6::MAX - 9)
                );
            }

            #[test]
            fn wrapping_mul() {
                assert_eq!(u6::new(5).wrapping_mul(2.into_lossy()), u6::new(10));
                assert_eq!(u6::new(32).wrapping_mul(2.into_lossy()), u6::new(0));
                assert_eq!(u6::new(10).wrapping_mul(10.into_lossy()), u6::new(36));
            }

            #[test]
            fn wrapping_div() {
                assert_eq!(u6::new(6).wrapping_div(2.into_lossy()), u6::new(3));
                assert_eq!(u6::new(10).wrapping_div(3.into_lossy()), u6::new(3));
                assert_eq!(u6::new(0).wrapping_div(3.into_lossy()), u6::new(0));
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
                assert_eq!(i6::new(10).saturating_add(5.into_lossy()), i6::new(15));
                assert_eq!(
                    i6::max_value().saturating_add(5.into_lossy()),
                    i6::max_value()
                )
            }

            #[test]
            fn saturating_sub() {
                assert_eq!(i6::new(10).saturating_sub(5.into_lossy()), i6::new(5));
                assert_eq!(
                    i6::min_value().saturating_sub(5.into_lossy()),
                    i6::min_value()
                )
            }

            #[test]
            fn saturating_mul() {
                assert_eq!(i6::new(10).saturating_mul(2.into_lossy()), i6::new(20));
                assert_eq!(i6::new(10).saturating_mul(10.into_lossy()), i6::max_value())
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