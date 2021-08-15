use crate::clamp::{clamped, Clamp, Wrap};
use crate::convert::{LossyFrom, UncheckedFrom, WrappingFrom};
use crate::error::{OutOfRangeIntError, ParseIntError};
use crate::non_standard_integer::{
    NonStandardInteger, NonStandardIntegerCommon, NonStandardIntegerSigned,
};
use core::convert::{From, TryFrom};
use core::fmt::{self, Display};
use core::str::FromStr;

/// Represents if an integer is considered to be signed
pub trait SignedInt<const SIGNED: bool> {
    /// If the integer is signed
    const SIGNED: bool = SIGNED;
}

/// An integer representation that can hold `BITS` amount of information for the given type `T`.
#[repr(transparent)]
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct int<T, const BITS: u32>(#[doc(hidden)] pub T);

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

    /// Gets the inner value
    pub fn val(self) -> T {
        self.0
    }
}

impl<T, const BITS: u32> FromStr for int<T, BITS>
where
    T: FromStr<Err = core::num::ParseIntError>,
    Self: TryFrom<T, Error = OutOfRangeIntError>,
{
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        T::from_str(s)
            .map(|v| Self::try_from(v).map_err(|e| e.into()))
            .map_err(|err| err.kind().clone().into())
            .flatten()
    }
}

/// Convert a `T` into the target without bounds checking
unsafe impl<T, const BITS: u32> const UncheckedFrom<T> for int<T, BITS> {
    unsafe fn from_unchecked(n: T) -> Self {
        Self(n)
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
pub macro impl_common($ty:ty, $signed:literal, { $($tt:tt)* }) {
    impl<const BITS: u32> const LossyFrom<$ty> for int<$ty, BITS> {
        /// Convert a `T` into the target. Only the `BITS` amount are kept.
        fn from_lossy(val: $ty) -> Self {
            unsafe {
                Clamp::<Self>::clamp(<Self as UncheckedFrom<$ty>>::from_unchecked(val))
            }
        }
    }

    impl<const BITS: u32> WrappingFrom<$ty> for int<$ty, BITS> {
        fn from_wrapping(n: $ty) -> Self {
            Self(n).wrap()
        }
    }

    impl<const BITS: u32> const Clamp<Self> for int<$ty, BITS> {
        fn clamp(self) -> Self {
            self.clamped().0
        }

        // todo: find better name
        /// Limits the inner value to be between `MIN` and `MAX`
        fn clamped(self) -> (Self, bool) {
            let (val, clamped) = clamped(*self.as_ref(), Self::MIN, Self::MAX);
            // SAFETY: the value has already been clamped to be in the valid range of `int`
            unsafe { (Self::from_unchecked(val), clamped) }
        }
    }

    impl<const BITS: u32> SignedInt<$signed> for int<$ty, BITS> {}

    /// ```
    /// use anyint::prelude::*;
    #[doc = concat!("let x = int::<", stringify!($ty), ", { ", stringify!(6), " }>::from_lossy(10);")]
    /// assert_eq!(x.as_ref(), &10);
    /// ```
    impl<const BITS: u32> const NonStandardIntegerCommon<$ty, BITS> for int<$ty, BITS> {
        // checked implementations are not based on overflowing implementations because they can be implemented independently a little more performant.
        // todo: check performance...
        fn_checked!(
            checked_add,
            checked_sub,
            checked_mul,
            checked_div,
            checked_rem,
        );

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(1).checked_shl(4), Some(N6::new(16)));
        /// assert_eq!(N6::new(1).checked_shl(128), None);
        /// ```
        fn checked_shl(self, rhs: u32) -> Option<Self> {
            let (a, b) = self.overflowing_shl(rhs);
            if b {None} else {Some(a)}
        }

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(16).checked_shr(4), Some(N6::new(1)));
        /// assert_eq!(N6::new(16).checked_shr(128), None);
        /// ```
        fn checked_shr(self, rhs: u32) -> Option<Self> {
            let (a, b) = self.overflowing_shr(rhs);
            if b {None} else {Some(a)}
        }

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

        // TODO: optimize generated asm, remove naive implementation
        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(20).wrapping_rem(N6::new(10)).0, 0);
        /// ```
        fn wrapping_rem(self, rhs: Self) -> Self {
            Self(self.0.wrapping_rem(rhs.0))
        }

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(1).wrapping_shl(4), N6::new(16));
        /// assert_eq!(N6::new(1).wrapping_shl(128), N6::new(1));
        /// ```
        fn wrapping_shl(self, rhs: u32) -> Self {
            Self(self.as_ref().wrapping_shl(rhs) & Self::MAX)
        }

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(16).wrapping_shr(4), N6::new(1));
        /// assert_eq!(N6::new(16).wrapping_shr(128), N6::new(16));
        /// ```
        fn wrapping_shr(self, rhs: u32) -> Self {
            Self(self.as_ref().wrapping_shr(rhs) & Self::MAX)
        }

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::max_value().overflowing_add(N6::from_lossy(1)), (N6::min_value(), true));
        /// assert_eq!(N6::min_value().overflowing_add(N6::from_lossy(1)), (N6::from_lossy(N6::MIN + 1), false));
        /// ```
        fn overflowing_add(self, rhs: Self) -> (Self, bool) {
            Self(*self.as_ref() + *rhs.as_ref()).wrapped()
        }

        /// ```
        /// use anyint::prelude::*;
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
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(1).overflowing_shl(4), (N6::new(16), false));
        /// assert_eq!(N6::new(1).overflowing_shl(128), (N6::new(1), true));
        /// ```
        fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shl(rhs), (rhs > (Self::BITS - 1)))
        }

        /// ```
        /// use anyint::prelude::*;
        #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
        /// assert_eq!(N6::new(16).overflowing_shr(4), (N6::new(1), false));
        /// assert_eq!(N6::new(16).overflowing_shr(128), (N6::new(16), true));
        /// ```
        fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shr(rhs), (rhs > (Self::BITS - 1)))
        }

        $($tt)*
    }

    impl<const BITS: u32> const TryFrom<$ty> for int<$ty, BITS>
    where
        Self: NonStandardInteger<$ty, BITS>,
    {
        type Error = OutOfRangeIntError;
        // todo: test for negatives
        fn try_from(data: $ty) -> Result<Self, Self::Error> {
            if data > Self::MAX {
                Err(OutOfRangeIntError::PosOverflow)
            }
            else if data < Self::MIN {
                Err(OutOfRangeIntError::NegOverflow)
            }
            else {
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

        impl<const BITS: u32> const NonStandardInteger<$ty, BITS> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS) - 1;
            const MIN: $ty = 0;
        }

        impl_common!($ty, false, {
            fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                (Self(self.0 % rhs.0) , false)
            }

            fn wrapping_rem(self, rhs: Self) -> Self {
                self.overflowing_rem(rhs).0
            }
        });
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

        impl<const BITS: u32> const NonStandardInteger<$ty, BITS> for int<$ty, BITS> {
            const MAX: $ty = (1 << Self::BITS.saturating_sub(1)) - 1;
            const MIN: $ty = !Self::MAX;
        }

        impl<const BITS: u32> const NonStandardIntegerSigned<$ty, BITS> for int<$ty, BITS> {
            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).is_negative(), false);
            /// assert_eq!(N6::new(-5).is_negative(), true);
            /// assert_eq!(N6::new(N6::MIN).is_negative(), true);
            /// assert_eq!(N6::new(N6::MAX).is_negative(), false);
            /// ```
            fn is_negative(self) -> bool {
                self.0.is_negative()
            }

            fn abs(self) -> Self {
                let (val, overflowed) = self.overflowing_abs();
                debug_assert!(!overflowed, "attempt to abs with overflow");
                val
            }

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

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).overflowing_neg(), (N6::new(-5), false));
            /// assert_eq!(N6::new(-5).overflowing_neg(), (N6::new(5), false));
            /// assert_eq!(N6::new(N6::MIN).overflowing_neg(), (N6::min_value(), true));
            /// ```
            fn overflowing_neg(self) -> (Self, bool) {
                if self.0 == Self::MIN {
                    (Self(Self::MIN), true)
                } else {
                    (Self(-self.0), false)
                }
            }

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).overflowing_abs(), (N6::new(5), false));
            /// assert_eq!(N6::new(-5).overflowing_abs(), (N6::new(5), false));
            /// assert_eq!(N6::new(N6::MIN).overflowing_abs(), (N6::min_value(), true));
            /// ```
            fn overflowing_abs(self) -> (Self, bool) {
                (self.wrapping_abs(), self.0 == Self::MIN)
            }

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).checked_neg(), Some(N6::new(-5)));
            /// assert_eq!(N6::new(-5).checked_neg(), Some(N6::new(5)));
            /// assert_eq!(N6::new(N6::MIN).checked_neg(), None);
            /// ```
            fn checked_neg(self) -> Option<Self> {
                let (a, b) = self.overflowing_neg();
                if b { None } else { Some(a) }
            }

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).checked_abs(), Some(N6::new(5)));
            /// assert_eq!(N6::new(-5).checked_abs(), Some(N6::new(5)));
            /// assert_eq!(N6::new(N6::MIN).checked_abs(), None);
            /// ```
            fn checked_abs(self) -> Option<Self> {
                if self.is_negative() {
                    self.checked_neg()
                } else {
                    Some(self)
                }
            }

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).wrapping_neg(), N6::new(-5));
            /// assert_eq!(N6::new(-5).wrapping_neg(),N6::new(5));
            /// assert_eq!(N6::new(N6::MIN).wrapping_neg(), N6::new(N6::MIN));
            /// ```
            fn wrapping_neg(self) -> Self {
                self.overflowing_neg().0
            }

            /// ```
            /// use anyint::prelude::*;
            #[doc = concat!("type N6 = int<", stringify!($ty), ", { ", stringify!(6), " }>;")]
            /// assert_eq!(N6::new(5).wrapping_abs(), N6::new(5));
            /// assert_eq!(N6::new(-5).wrapping_abs(),N6::new(5));
            /// assert_eq!(N6::new(N6::MIN).wrapping_abs(), N6::new(N6::MIN));
            /// ```
            fn wrapping_abs(self) -> Self {
                if self.is_negative() {
                    self.wrapping_neg()
                } else {
                    self
                }
            }
        }

        impl_common!($ty, true, {
            fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                if self.0 == Self::MIN && rhs.0 == -1 {
                    (Self(0), true)
                } else {
                    (Self(self.0 % rhs.0), false)
                }
            }

            fn wrapping_rem(self, rhs: Self) -> Self {
                self.overflowing_rem(rhs).0
            }
        });
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
    /// use anyint::prelude::*;
    /// let x = anyint::int::<i8, 8>::MAX;
    /// ```
    pub struct SIntOnlyTakesValidSize;

    /// ```compile_fail
    /// use anyint::prelude::*;
    /// let x = anyint::int::<u8, 8>::MAX;
    /// ```
    pub struct UIntOnlyTakesValidSize;

    /// ```
    /// use anyint::prelude::*;
    /// let x = int::<u8, 7>::MAX;
    /// let x = int::<i8, 7>::MAX;
    /// ```
    pub struct IntTakesValidSizes;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::convert::LossyInto;
    use core::convert::TryInto;

    #[allow(non_camel_case_types)]
    type u6 = int<u8, 6>;

    #[allow(non_camel_case_types)]
    type i6 = int<i8, 6>;

    #[test]
    fn type_inference() {
        let _: int<u8, 6> = int::from_lossy(5);
        let _: int<i32, 15> = int::from_lossy(5);
    }

    #[test]
    fn from_wrapping() {
        let x: int<u8, 6> = int::from_wrapping(65);
        assert_eq!(x.as_ref(), &1);
        let y: int<i8, 6> = int::from_wrapping(33);
        assert_eq!(y.as_ref(), &-31);
    }

    mod unsigned_common {
        use super::*;

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
            assert_eq!(value, Err(OutOfRangeIntError::PosOverflow))
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

            mod traits {
                use super::*;

                #[test]
                fn from_str() {
                    assert_eq!(u6::from_str(""), Err(ParseIntError::Empty));
                    assert_eq!(u6::from_str("10"), Ok(u6::new(10)));
                    assert_eq!(u6::from_str("-10"), Err(ParseIntError::InvalidDigit));
                    assert_eq!(
                        u6::from_str("64"),
                        Err(ParseIntError::OutOfRange(OutOfRangeIntError::PosOverflow))
                    );
                }
            }
        }
    }

    mod signed {
        use super::*;

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
            assert_eq!(value, Err(OutOfRangeIntError::PosOverflow));

            let value: Result<i6, OutOfRangeIntError> = (-33).try_into();
            assert_eq!(value, Err(OutOfRangeIntError::NegOverflow))
        }

        #[test]
        #[cfg(not(debug_assertions))]
        fn abs() {
            let a = i6::min_value().abs();
            assert_eq!(a, u6::min_value());
        }

        #[test]
        #[should_panic]
        #[cfg(debug_assertions)]
        fn abs() {
            let _ = i6::min_value().abs();
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
            fn overflowing_rem() {
                assert_eq!(
                    i6::new(6).overflowing_rem(2.into_lossy()),
                    (i6::new(0), false)
                );
                assert_eq!(
                    i6::new(i6::MIN).overflowing_rem(i6::new(-1)),
                    (i6::new(0), true)
                );
            }

            #[test]
            #[should_panic]
            fn overflowing_div_with_zero() {
                i6::new(3).overflowing_div(0.into_lossy());
            }
        }

        mod wrapping {
            use super::*;

            #[test]
            fn wrapping_rem() {
                assert_eq!(i6::new(20).wrapping_rem(i6::new(10)).0, 0);
                assert_eq!(i6::new(i6::MIN).wrapping_rem(i6::new(-1)).0, 0);
                assert_eq!(i6::new(i6::MIN).wrapping_rem(i6::new(-2)).0, 0);
            }
        }

        mod traits {
            use super::*;

            #[test]
            fn from_str() {
                assert_eq!(i6::from_str("10"), Ok(i6::new(10)));
                assert_eq!(i6::from_str("-10"), Ok(i6::new(-10)));
                assert_eq!(
                    i6::from_str("-33"),
                    Err(ParseIntError::OutOfRange(OutOfRangeIntError::NegOverflow))
                );
                assert_eq!(
                    i6::from_str("32"),
                    Err(ParseIntError::OutOfRange(OutOfRangeIntError::PosOverflow))
                );
                assert_eq!(i6::from_str(""), Err(ParseIntError::Empty));
            }
        }
    }
}
