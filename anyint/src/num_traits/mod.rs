use crate::convert::UncheckedFrom;
use crate::integer::int;
use crate::non_standard_integer::{NonStandardInteger, NonStandardIntegerCommon};

use num_traits::{
    AsPrimitive, Bounded, CheckedAdd, CheckedDiv, CheckedMul, CheckedShl, CheckedShr, CheckedSub,
    FromPrimitive, One, SaturatingAdd, SaturatingMul, SaturatingSub, ToPrimitive, WrappingAdd,
    WrappingMul, WrappingSub, Zero,
};

impl<T, const BITS: u32> Bounded for int<T, BITS>
where
    T: PartialOrd + Copy,
    Self: NonStandardInteger<T, BITS>,
{
    fn min_value() -> Self {
        NonStandardInteger::<T, BITS>::min_value()
    }

    fn max_value() -> Self {
        NonStandardInteger::<T, BITS>::max_value()
    }
}

impl<T, const BITS: u32> AsPrimitive<T> for int<T, BITS>
where
    T: 'static + PartialOrd + Copy,
    Self: NonStandardInteger<T, BITS>,
{
    fn as_(self) -> T {
        self.0
    }
}

impl<T, const BITS: u32> FromPrimitive for int<T, BITS>
where
    T: PartialOrd + Copy + AsPrimitive<i64> + From<i64> + AsPrimitive<u64> + From<u64>,
    Self: NonStandardInteger<T, BITS> + UncheckedFrom<T>,
{
    fn from_u64(n: u64) -> Option<Self> {
        let min: u64 = Self::MIN.as_();
        let max: u64 = Self::MAX.as_();
        (min <= n && n < max).then(|| unsafe { Self::from_unchecked(n.into()) })
    }

    fn from_i64(n: i64) -> Option<Self> {
        let min: i64 = Self::MIN.as_();
        let max: i64 = Self::MAX.as_();
        (min <= n && n < max).then(|| unsafe { Self::from_unchecked(n.into()) })
    }
}

impl<T, const BITS: u32> ToPrimitive for int<T, BITS>
where
    T: PartialOrd + Copy + ToPrimitive,
    Self: NonStandardInteger<T, BITS>,
{
    fn to_i64(&self) -> Option<i64> {
        self.0.to_i64()
    }

    fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }
}

impl<T, const BITS: u32> One for int<T, BITS>
where
    T: PartialOrd + Copy + One,
    Self: NonStandardIntegerCommon<T, BITS> + UncheckedFrom<T>,
{
    fn one() -> Self {
        // lazy
        Self(One::one())
    }
}

impl<T, const BITS: u32> Zero for int<T, BITS>
where
    T: PartialOrd + Copy + Zero,
    Self: NonStandardIntegerCommon<T, BITS> + UncheckedFrom<T>,
{
    fn zero() -> Self {
        // lazy
        Self(Zero::zero())
    }

    fn is_zero(&self) -> bool {
        self.0 == Zero::zero()
    }
}

#[doc(hidden)]
/// Forward methods from `NonStandardIntegerCommon` for num-traits
pub macro num_trait_impl($trait_name:ident, $method:ident, $ty:ty) {
    impl<T, const BITS: u32> $trait_name for int<T, BITS>
    where
        T: PartialOrd + Copy,
        Self: NonStandardIntegerCommon<T, BITS>,
    {
        #[inline]
        fn $method(&self, v: &Self) -> $ty {
            <Self as NonStandardIntegerCommon<T, BITS>>::$method(*self, *v)
        }
    }
}

#[doc(hidden)]
/// Forward shr and shl methods from `NonStandardIntegerCommon` for num-traits
pub macro num_trait_shift_impl($trait_name:path, $method:ident, $ty:ty) {
    impl<T, const BITS: u32> $trait_name for int<T, BITS>
    where
        T: PartialOrd + Copy,
        Self: NonStandardIntegerCommon<T, BITS>,
    {
        #[inline]
        fn $method(&self, v: u32) -> $ty {
            <Self as NonStandardIntegerCommon<T, BITS>>::$method(*self, v)
        }
    }
}

num_trait_impl!(CheckedAdd, checked_add, Option<Self>);
num_trait_impl!(CheckedSub, checked_sub, Option<Self>);
num_trait_impl!(CheckedMul, checked_mul, Option<Self>);
num_trait_impl!(CheckedDiv, checked_div, Option<Self>);
// checked_impl!(num_traits::CheckedRem, checked_rem);
num_trait_shift_impl!(CheckedShl, checked_shl, Option<Self>);
num_trait_shift_impl!(CheckedShr, checked_shr, Option<Self>);

num_trait_impl!(WrappingAdd, wrapping_add, Self);
num_trait_impl!(WrappingSub, wrapping_sub, Self);
num_trait_impl!(WrappingMul, wrapping_mul, Self);
// num_trait_shift_impl!(num_traits::WrappingShl, wrapping_shl, Self);
// num_trait_shift_impl!(num_traits::WrappingShr, wrapping_shr, Self);

num_trait_impl!(SaturatingAdd, saturating_add, Self);
num_trait_impl!(SaturatingSub, saturating_sub, Self);
num_trait_impl!(SaturatingMul, saturating_mul, Self);

#[cfg(test)]
mod tests {
    #![allow(non_camel_case_types)]

    use super::*;
    type u6 = int<u8, 6>;

    #[test]
    fn as_primative() {
        let n = u6::new(5);
        assert_eq!(AsPrimitive::as_(n), 5)
    }

    fn checked_add() {
        let n = u6::new(5);
        assert_eq!(CheckedAdd::checked_add(&n, &n), Some(u6::new(10)))
    }
}
