use crate::integer::int;
use crate::non_standard_integer::NonStandardIntegerCommon;

use core::ops::{Add, Div, Mul, Shl, Shr, Sub};

#[doc(hidden)]
pub macro impl_op($trait_name: ident, $trait_fn_name: ident ($rhs_ty: ty), $overflow_name: ident, $overflow_message: literal) {
    impl<T: PartialOrd + Copy, const BITS: u32> $trait_name<$rhs_ty> for int<T, BITS>
    where
        Self: NonStandardIntegerCommon<T, BITS>,
    {
        type Output = Self;
        fn $trait_fn_name(self, rhs: $rhs_ty) -> Self::Output {
            let (val, overflowed) = self.$overflow_name(rhs);
            debug_assert!(!overflowed, $overflow_message);
            val
        }
    }
}

impl_op!(
    Add,
    add(Self),
    overflowing_add,
    "attempt to add with overflow"
);
impl_op!(
    Sub,
    sub(Self),
    overflowing_sub,
    "attempt to subtract with overflow"
);
impl_op!(
    Mul,
    mul(Self),
    overflowing_mul,
    "attempt to multiply with overflow"
);
impl_op!(
    Div,
    div(Self),
    overflowing_div,
    "attempt to divide with overflow"
);
impl_op!(
    Shr,
    shr(u32),
    overflowing_shr,
    "attempt to shift right with overflow"
);
impl_op!(
    Shl,
    shl(u32),
    overflowing_shl,
    "attempt to shift left with overflow"
);

#[cfg(test)]
mod test {
    use super::*;

    #[allow(non_camel_case_types)]
    type u6 = int<u8, 6>;

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn add() {
        let a = u6::new(32);
        let b = u6::new(32);
        assert_eq!(a + b, u6::new(0));
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn add() {
        let a = u6::new(32);
        let b = u6::new(32);
        assert_eq!(a + b, u6::new(0));
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn sub() {
        let a = u6::new(32);
        let b = u6::new(32);
        assert_eq!(a - b, u6::new(0));
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn mul() {
        let a = u6::new(2);
        let b = u6::new(32);
        assert_eq!(a * b, u6::new(0));
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn div() {
        let a = u6::new(9);
        let b = u6::new(3);
        assert_eq!(a / b, u6::new(3));
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn shl() {
        let _ = u6::new(1) << 6;
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn shl() {
        assert_eq!(u6::new(1) << 4, u6::new(16));
        assert_eq!((u6::new(1) << 5), u6::new(32));
        assert_eq!((u6::new(1) << 6), u6::new(0));
        assert_eq!((u6::new(3) << 3), u6::new(24));
        assert_eq!((u6::new(3) << 5), u6::new(32));
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn shr() {
        let _ = u6::new(1) >> 6;
    }

    #[test]
    #[cfg(not(debug_assertions))]
    fn shr() {
        assert_eq!(u6::new(4) >> 1, u6::new(2));
        assert_eq!(u6::new(63) >> 7, u6::new(0));
    }
}
