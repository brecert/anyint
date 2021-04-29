use crate::{int, NonStandardIntegerExt};
use std::ops::{Add, Div, Mul, Sub};

impl<T: PartialOrd + Copy, const BITS: u32> Add for int<T, BITS>
where
  Self: NonStandardIntegerExt<T, BITS, false>,
{
  type Output = Self;

  fn add(self, rhs: Self) -> Self::Output {
    let (val, overflowed) = self.overflowing_add(rhs);
    debug_assert!(!overflowed, "attempt to add with overflow");
    val
  }
}

impl<T: PartialOrd + Copy, const BITS: u32> Sub for int<T, BITS>
where
  Self: NonStandardIntegerExt<T, BITS, false>,
{
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
    let (val, overflowed) = self.overflowing_sub(rhs);
    debug_assert!(!overflowed, "attempt to subtract with overflow");
    val
  }
}

impl<T: PartialOrd + Copy, const BITS: u32> Mul for int<T, BITS>
where
  Self: NonStandardIntegerExt<T, BITS, false>,
{
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    let (val, overflowed) = self.overflowing_mul(rhs);
    debug_assert!(!overflowed, "attempt to multiply with overflow");
    val
  }
}

impl<T: PartialOrd + Copy, const BITS: u32> Div for int<T, BITS>
where
  Self: NonStandardIntegerExt<T, BITS, false>,
{
  type Output = Self;

  fn div(self, rhs: Self) -> Self::Output {
    let (val, overflowed) = self.overflowing_div(rhs);
    debug_assert!(!overflowed, "attempt to divide with overflow");
    val
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::LossyFrom;

  #[allow(non_camel_case_types)]
  type u6 = int<u8, 6>;

  #[test]
  #[should_panic]
  #[cfg(debug_assertions)]
  fn add() {
    let a = u6::from_lossy(32);
    let b = u6::from_lossy(32);
    assert_eq!(a + b, u6::from_lossy(0));
  }

  #[test]
  #[cfg(not(debug_assertions))]
  fn add() {
    let a = u6::from_lossy(32);
    let b = u6::from_lossy(32);
    assert_eq!(a + b, u6::from_lossy(0));
  }

  #[test]
  #[cfg(not(debug_assertions))]
  fn sub() {
    let a = u6::from_lossy(32);
    let b = u6::from_lossy(32);
    assert_eq!(a - b, u6::from_lossy(0));
  }

  #[test]
  #[cfg(not(debug_assertions))]
  fn mul() {
    let a = u6::from_lossy(2);
    let b = u6::from_lossy(32);
    assert_eq!(a * b, u6::from_lossy(0));
  }

  #[test]
  #[cfg(not(debug_assertions))]
  fn div() {
    let a = u6::from_lossy(9);
    let b = u6::from_lossy(3);
    assert_eq!(a / b, u6::from_lossy(3));
  }
}
