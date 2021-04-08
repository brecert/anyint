// todo: no std
use std::convert::{From, TryFrom};
use thiserror::Error;

#[derive(Error, Debug, Copy, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[error("out of range type conversion attempted")]
pub struct OutOfRangeIntError;

// decl 1.0 because consts didn't work with 2.0 and supporting older rust
macro_rules! implement_common {
    ($name: ident, $ty: ty) => {
        impl<const N: u8> $name<N> {
            #[inline]
            /// Returns the largest value that can be represented by this integer type.
            pub const fn max_value() -> Self {
                Self(Self::MAX)
            }

            #[inline]
            /// Returns the smallest value that can be represented by this integer type.
            pub const fn min_value() -> Self {
                Self(Self::MIN)
            }

            #[inline]
            pub const unsafe fn from_unchecked(data: $ty) -> Self {
                Self(data)
            }

            #[inline]
            pub const fn from_lossy(data: $ty) -> Self {
                Self(data & Self::MAX)
            }
        }

        impl<const N: u8> From<$name<N>> for $ty {
            #[inline]
            fn from(data: $name<N>) -> $ty {
                data.0
            }
        }

        impl<const N: u8> TryFrom<$ty> for $name<N> {
            type Error = OutOfRangeIntError;

            #[inline]
            fn try_from(data: $ty) -> Result<Self, Self::Error> {
                if data > <$ty>::from(Self::MAX) {
                    Err(OutOfRangeIntError)
                } else {
                    Ok(Self(data))
                }
            }
        }
    };
}

macro_rules! impl_arbitray_unsigned_int {
    ($name: ident, $ty: ty) => {
        #[repr(transparent)]
        #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
        pub struct $name<const N: u8>($ty);

        impl<const N: u8> $name<N> {
            pub const MAX: $ty = (1 << N) - 1;
            pub const MIN: $ty = 0;
            pub const BITS: u8 = N;
        }

        implement_common!($name, $ty);
    };
}

macro_rules! impl_arbitray_signed_int {
    ($name: ident, $ty: ty) => {
        #[repr(transparent)]
        #[derive(Copy, Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
        pub struct $name<const N: u8>($ty);

        impl<const N: u8> $name<N> {
            pub const MAX: $ty = (1 << N - 1) - 1;
            pub const MIN: $ty = !Self::MAX;
            pub const BITS: u8 = N;
        }

        implement_common!($name, $ty);
    };
}

impl_arbitray_unsigned_int!(U8, u8);
impl_arbitray_unsigned_int!(U16, u16);
impl_arbitray_unsigned_int!(U32, u32);
impl_arbitray_unsigned_int!(U64, u64);
impl_arbitray_unsigned_int!(USize, usize);

impl_arbitray_signed_int!(I8, i8);
impl_arbitray_signed_int!(I16, i16);
impl_arbitray_signed_int!(I32, i32);
impl_arbitray_signed_int!(I64, i64);
impl_arbitray_signed_int!(ISize, isize);

#[cfg(test)]
mod test {
    use super::*;
    use std::convert::TryInto;

    mod unsigned {
        use super::*;

        #[test]
        fn max() {
            assert_eq!(U8::<6>::MAX, 63u8);
        }

        #[test]
        fn min() {
            assert_eq!(U8::<6>::MIN, 0u8);
        }

        #[test]
        fn bits() {
            assert_eq!(U8::<6>::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(U8::<6>::max_value(), U8::<6>(63));
        }

        #[test]
        fn min_value() {
            assert_eq!(U8::<6>::min_value(), U8::<6>(0));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value: U8<6> = U8::from_unchecked(u8::MAX);
                let value_u8: u8 = value.into();
                assert_eq!(value_u8, 255u8);
            }
        }

        #[test]
        fn from_lossy() {
            let value: U8<6> = U8::from_lossy(u8::MAX);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 63u8);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: U8<6> = U8(15);
            let value_u8: u8 = value.into();
            assert_eq!(value_u8, 15u8);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<U8<6>, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(U8::<6>(15)));
            let value: Result<U8<6>, OutOfRangeIntError> = 64.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }
    }

    mod signed {
        use super::*;

        #[test]
        fn max() {
            assert_eq!(I8::<6>::MAX, 31);
        }

        #[test]
        fn min() {
            assert_eq!(I8::<6>::MIN, -32);
        }

        #[test]
        fn bits() {
            assert_eq!(I8::<6>::BITS, 6);
        }

        #[test]
        fn max_value() {
            assert_eq!(I8::<6>::max_value(), I8::<6>(31));
        }

        #[test]
        fn min_value() {
            assert_eq!(I8::<6>::min_value(), I8::<6>(-32));
        }

        #[test]
        fn from_unchecked() {
            unsafe {
                let value: I8<6> = I8::from_unchecked(i8::MAX);
                let value_i8: i8 = value.into();
                assert_eq!(value_i8, 127);
            }
        }

        #[test]
        fn from_lossy() {
            let value: I8<6> = I8::from_lossy(i8::MAX);
            let value_i8: i8 = value.into();
            assert_eq!(value_i8, 31);
        }

        #[test]
        fn from_arbitrary_to_inner() {
            let value: I8<6> = I8(15);
            let value_i8: i8 = value.into();
            assert_eq!(value_i8, 15);
        }

        #[test]
        fn try_from_inner_type_to_arbitrary() {
            let value: Result<I8<6>, OutOfRangeIntError> = 15.try_into();
            assert_eq!(value, Ok(I8::<6>(15)));
            let value: Result<I8<6>, OutOfRangeIntError> = 32.try_into();
            assert_eq!(value, Err(OutOfRangeIntError))
        }
    }
}
