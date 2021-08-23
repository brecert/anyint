//! Macros to make constructing `int` types and values easier.

// TODO: Explain hygeine

/// Macro for constructing [`anyint::int`] instances.
///
/// # Syntax
///
/// Syntax is similar to the currently existing rust integer literals, however there are differences.
///
/// Any value in the range `0..=127` can be used for the width of the [`crate::int`]
///
/// However, `size` is not a valid size for the width.
///
/// # Examples
///
/// ```rust
/// use anyint::macros::int;
/// use anyint::integer::int;
///
/// assert_eq!(int!(0u6), int::<u8, 6>::new(0));
/// assert_eq!(int!(-32i6), int::<i8, 6>::new(-32));
/// ```
pub use anyint_macros::int;

/// Macro for using [`anyint::int`] types.
///
/// # Syntax
///
/// Syntax is similar to the currently existing rust integer types, however there are differences.
///
/// Any value in the range `0..=127` can be used for the width of the [`crate::int`]
///
/// However, `size` is not a valid size for the width.
///
/// # Examples
///
/// ```rust
/// use anyint::prelude::*;
/// use anyint::macros::Int;
///
/// fn add(a: u8, b: u8) -> Int![u12] {
///   int::new(a.into()) + int::new(b.into())
/// }
/// ```
pub use anyint_macros::Int;

#[cfg(test)]
mod test {
    use super::*;
    use crate::prelude::*;

    #[test]
    fn int_macro_uint() {
        assert_eq!(int!(0u6), int::<u8, 6>::new(0));
        assert_eq!(int!(63u6), int::<u8, 6>::new(63));

        assert_eq!(int!(0u127), int::<u128, 127>::new(0));
    }

    #[test]
    fn int_macro_sint() {
        assert_eq!(int!(31i6), int::<i8, 6>::new(31));
        assert_eq!(int!(-32i6), int::<i8, 6>::new(-32));

        assert_eq!(int!(0i127), int::<i128, 127>::new(0));
    }

    #[test]
    fn type_macro() {
        assert_eq!(<Int![u6]>::MAX, int::<u8, 6>::MAX);
        assert_eq!(<Int![i6]>::MIN, -32);
        assert_eq!(<Int![i31]>::new(16), int::<i32, 31>::new(16));
    }
}

#[cfg(doctest)]
mod doctest {
    // TODO: test compiler errors that are generated to make sure they are accurate

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = int!(64u6);
    /// ```
    pub struct MacroOnlyTakesValidPositiveUInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = int!(-1u6);
    /// ```
    pub struct MacroOnlyTakesValidNegativeUInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = int!(32i6);
    /// ```
    pub struct MacroOnlyTakesValidPositiveSInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = int!(-33i6);
    /// ```
    pub struct MacroOnlyTakesValidNegativeSInt;

    /// ```compile_fail
    /// use anyint_macros::n;
    /// let x = int!(0u128);
    /// ```
    pub struct MacroOnlyTakesValidWidth;
}
