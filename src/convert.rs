/// Converts `Self` into `T`, possibly wrapping around in the process.
pub trait WrappingInto<T>: Sized {
    /// Performs the conversion, possibly wrapping around in the process.
    fn into_wrapping(self) -> T;
}

/// Creates `Self` from `T`, possibly wrapping around in the process.
pub trait WrappingFrom<T>: Sized {
    /// Performs the conversion, possibly losing data in the process.
    fn from_wrapping(_: T) -> Self;
}

impl<T, U> WrappingInto<U> for T
where
    U: WrappingFrom<T>,
{
    fn into_wrapping(self) -> U {
        U::from_wrapping(self)
    }
}

/// Converts `Self` into `T`, possibly losing data in the process.
pub trait LossyInto<T>: Sized {
    /// Performs the conversion, possibly losing data in the process.
    fn into_lossy(self) -> T;
}

/// Creates `Self` from `T`, possibly losing data in the process.
pub trait LossyFrom<T>: Sized {
    /// Performs the conversion, possibly losing data in the process.
    fn from_lossy(_: T) -> Self;
}

impl<T, U> LossyInto<U> for T
where
    U: LossyFrom<T>,
{
    fn into_lossy(self) -> U {
        U::from_lossy(self)
    }
}

/// Converts `Self` into `T`, without bound checking.
pub unsafe trait UncheckedInto<T>: Sized {
    /// Performs the conversion without checking, possibly performing undefined behavior in the process.
    unsafe fn into_unchecked(self) -> T;
}

/// Convert a `T` into the target without bounds checking.
pub unsafe trait UncheckedFrom<T>: Sized {
    /// Performs the conversion without checking, possibly performing undefined behavior in the process.
    unsafe fn from_unchecked(_: T) -> Self;
}

unsafe impl<T, U> UncheckedInto<U> for T
where
    U: UncheckedFrom<T>,
{
    unsafe fn into_unchecked(self) -> U {
        U::from_unchecked(self)
    }
}
