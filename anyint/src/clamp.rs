/// Provides wrapping or overflowing functionality to a value.
pub trait Wrap<T>: Sized {
    /// Wraps the value, wrapping around if out of bounds.
    fn wrap(self) -> T;

    /// Returns a tuple of the wrapped result, along with a boolean indicating whether the result was wrapped.
    fn wrapped(self) -> (T, bool);
}

/// Provides clamping functionality to a value.
pub trait Clamp<T>: Sized {
    /// Clamps the value, clamping at the bounds if the result is out of bounds.
    fn clamp(self) -> T;

    /// Returns a tuple of the clamped result, along with a boolean indicating whether the result was clamped.
    fn clamped(self) -> (T, bool);
}
