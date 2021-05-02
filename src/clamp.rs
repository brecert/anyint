/// Clamps a value between a range's beginning and end
pub const fn clamp<T: PartialOrd + Copy>(range: &std::ops::Range<T>, value: T) -> T {
  if value < range.start {
    return range.start;
  }
  if value > range.end {
    return range.end;
  }
  value
}

// pub trait Clamp<T> {
//   type Output = T;
//   fn clamp(&self, lhs: T) -> Self::Output;
// }

// impl<T: PartialOrd + Copy> const Clamp<T> for Range<T> {
//   #[inline]
//   fn clamp(&self, val: T) -> Self::Output {
//     clamp(self, val)
//   }
// }

/// Provides wrapping or overflowing functionality to a value.
pub trait Wrap<T>: Sized {
  type Output = T;

  #[inline]
  /// Wraps the value, wrapping around if out of bounds.
  fn wrap(self) -> Self::Output {
    self.wrapped().0
  }

  fn wrapped(self) -> (Self::Output, bool);
}
