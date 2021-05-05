/// Clamps a value between a range's beginning and end
#[inline]
pub const fn clamp<T: PartialOrd + Copy>(input: T, min: T, max: T) -> T {
  if input < min {
    min
  } else if input > max {
    max
  } else {
    input
  }
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
  /// The resulting type after wrapping.
  type Output = T;

  #[inline]
  /// Wraps the value, wrapping around if out of bounds.
  fn wrap(self) -> Self::Output {
    self.wrapped().0
  }

  /// Returns a tuple of the wrapped result, along with a boolean indicating whether the result was wrapped.
  fn wrapped(self) -> (Self::Output, bool);
}
