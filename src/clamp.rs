/// Clamps a value between a range's beginning and end
#[inline]
pub const fn clamped<T: PartialOrd + Copy>(input: T, min: T, max: T) -> (T, bool) {
    if input < min {
        (min, true)
    } else if input > max {
        (max, true)
    } else {
        (input, false)
    }
}

/// Provides wrapping or overflowing functionality to a value.
pub trait Wrap<T>: Sized {
    #[inline]
    /// Wraps the value, wrapping around if out of bounds.
    fn wrap(self) -> T {
        self.wrapped().0
    }

    /// Returns a tuple of the wrapped result, along with a boolean indicating whether the result was wrapped.
    fn wrapped(self) -> (T, bool);
}

/// Provides clamping functionality to a value.
pub trait Clamp<T>: Sized {
    #[inline]
    /// Clamps the value, clamping at the bounds if the result is out of bounds.
    fn clamp(self) -> T {
        self.clamped().0
    }

    /// Returns a tuple of the clamped result, along with a boolean indicating whether the result was clamped.
    fn clamped(self) -> (T, bool);
}
