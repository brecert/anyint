use std::ops::Range;

pub const fn clamp<T: PartialOrd + Copy>(range: &std::ops::Range<T>, val: T) -> T {
  if val < range.start {
    return range.start;
  }
  if val > range.end {
    return range.end;
  }
  return val;
}

pub trait Clamp<T> {
  type Output = T;
  fn clamp(&self, lhs: T) -> Self::Output;
}

impl<T: PartialOrd + Copy> const Clamp<T> for Range<T> {
  fn clamp(&self, val: T) -> Self::Output {
    clamp(self, val)
  }
}

/// Provides wrapping or overflowing functionality to a value.
pub trait Wrap<T>: Sized {
  type Output = T;
  #[inline]
  fn wrap(self) -> Self::Output {
    self.wrapped().0
  }

  fn wrapped(self) -> (Self::Output, bool);
}
