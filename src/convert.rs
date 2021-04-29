use std::convert::From;

pub trait WrappingInto<T>: Sized {
  /// Performs the conversion, possibly wrapping around in the process.
  fn into_wrapping(self) -> T;
}

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

pub trait LossyInto<T>: Sized {
  /// Performs the conversion, possibly losing data in the process.
  fn into_lossy(self) -> T;
}

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

impl<T, U> LossyFrom<U> for T
where
  T: From<U>,
{
  fn from_lossy(other: U) -> Self {
    Self::from(other)
  }
}

pub unsafe trait UncheckedInto<T>: Sized {
  /// Performs the conversion without checking, possibly performing undefined behavior in the process.
  unsafe fn into_unchecked(self) -> T;
}

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
