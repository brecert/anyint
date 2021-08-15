use crate::convert::UncheckedFrom;

// todo: const trait implementations
// todo: maybe default implementations should not require `Self` traits
/// Provides a base implementation for what a `NonStandardInteger` needs.
pub trait NonStandardInteger<T, const BITS: u32>
where
    T: PartialOrd + Copy,
    Self: UncheckedFrom<T>,
{
    // TODO: find a better name for this.
    /// The underlying representation of the integer.
    type Repr = T;

    /// The size of this integer type in bits.
    const BITS: u32 = BITS;

    /// The smallest value that can be represented by this integer type.
    const MIN: T;

    /// The largest value that can be represented by this integer type.
    const MAX: T;

    /// Returns the smallest value that can be represented by this integer type.
    fn min_value() -> Self {
        // SAFETY: The user ensures that `MIN` is valid
        unsafe { Self::from_unchecked(Self::MIN) }
    }
    /// Returns the largest value that can be represented by this integer type.
    fn max_value() -> Self {
        // SAFETY: The user ensures that `MAX` is valid
        unsafe { Self::from_unchecked(Self::MAX) }
    }
}

/// Provides integer methods.
pub trait NonStandardIntegerCommon<T: PartialOrd + Copy, const BITS: u32>
where
    Self: NonStandardInteger<T, BITS>,
{
    /// Checked integer addition. Computes `self + rhs`, returning `None`
    /// if overflow occurred.
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs`, returning `None`
    /// if overflow occurred.
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked integer remainder. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    /// Checked shift left. Computes `self << rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right. Computes `self >> rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    fn checked_shr(self, rhs: u32) -> Option<Self>;

    // fn checked_pow(self, rhs: u32) -> Self;

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_add(self, rhs: Self) -> Self;

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_sub(self, rhs: Self) -> Self;

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds instead of overflowing.
    fn saturating_mul(self, rhs: Self) -> Self;

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric bounds instead of overflowing.
    fn saturating_pow(self, exp: u32) -> Self;

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the
    /// boundary of the type.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the
    /// boundary of the type.
    fn wrapping_sub(self, rhs: Self) -> Self;

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at
    /// the boundary of the type.
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the
    /// boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one divides `MIN / -1` on a signed type (where
    /// `MIN` is the negative minimal value for the type); this is equivalent to `-MIN`, a positive value
    /// that is too large to represent in the type. In such a case, this function returns `MIN` itself.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn wrapping_div(self, rhs: Self) -> Self;

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at the
    /// boundary of the type.
    ///
    /// Such wrap-around never actually occurs mathematically;
    /// implementation artifacts make `x % y` invalid for `MIN / -1` on a signed type (where `MIN` is the negative minimal value).
    /// In such a case, this function returns `0`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn wrapping_rem(self, rhs: Self) -> Self;

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    fn wrapping_shl(self, rhs: u32) -> Self;

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    fn wrapping_shr(self, rhs: u32) -> Self;

    // fn wrapping_pow(self, exp: u32) -> Self;

    /// Calculates `self` + `rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would
    /// occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_add(self, rhs: Self) -> (Self, bool);

    /// Calculates `self` - `rhs`
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic overflow
    /// would occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic overflow
    /// would occur. If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would
    /// occur. If an overflow would occur then self is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn overflowing_div(self, rhs: Self) -> (Self, bool);

    /// Calculates the remainder when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean indicating whether an
    /// arithmetic overflow would occur. If an overflow would occur then 0 is returned.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    fn overflowing_rem(self, rhs: Self) -> (Self, bool);

    /// Shifts self left by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of self along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked `(BITS - 1)` where N is the number of bits, and this value is then
    /// used to perform the shift.
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);

    /// Shifts self right by `rhs` bits.
    ///
    /// Returns a tuple of the shifted version of self along with a boolean
    /// indicating whether the shift value was larger than or equal to the
    /// number of bits. If the shift value is too large, then value is
    /// masked `(BITS - 1)`, and this value is then
    /// used to perform the shift.
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);

    // fn overflowing_pow(self, exp: u32) -> Self;
}

/// Provides integer methods that only make sense with signed integers.
pub trait NonStandardIntegerSigned<T: PartialOrd + Copy, const BITS: u32>
where
    Self: NonStandardInteger<T, BITS>,
{
    /// Computes the absolute value of `self`.
    ///
    /// # Overflow behavior
    ///
    /// The absolute value of `MIN` cannot be represented as a value in signed integers.
    ///
    /// Attempting to calculate it will cause an overflow. This means
    /// that code in debug mode will trigger a panic on this case and
    /// optimized code will return `MIN` without a panic.
    fn abs(self) -> Self;

    /// Returns `true` if `self` is negative and `false` if the number is zero or
    /// positive.
    fn is_negative(self) -> bool;

    /// Saturating integer negation. Computes `-self`, returning `MAX`
    /// if `self == MIN` instead of overflowing.
    fn saturating_neg(self) -> Self;

    /// Saturating absolute value. Computes `self.abs()`, returning `MAX`
    /// if `self == MIN` instead of overflowing.
    fn saturating_abs(self) -> Self;

    /// Negates self, overflowing if this is equal to the minimum value.
    ///
    /// Returns a tuple of the negated version of self along with a boolean indicating whether an overflow
    /// happened. If `self` is the minimum value `MIN`, then the
    /// minimum value will be returned again and `true` will be returned for an overflow happening.
    fn overflowing_neg(self) -> (Self, bool);

    /// Computes the absolute value of `self`.
    ///
    /// Returns a tuple of the absolute version of self along with a boolean indicating whether an overflow
    /// happened. If self is the minimum value `MIN` then the value will be returned
    /// again and true will be returned for an overflow happening.
    fn overflowing_abs(self) -> (Self, bool);

    /// Checked negation. Computes `-self`, returning `None` if `self == MIN`.
    fn checked_neg(self) -> Option<Self>;

    /// Checked absolute value. Computes `self.abs()`, returning `None` if
    /// `self == MIN`
    fn checked_abs(self) -> Option<Self>;

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary
    /// of the type.
    ///
    /// The only case where such wrapping can occur is when one negates `MIN` on a signed type (where `MIN`
    /// is the negative minimal value for the type); this is a positive value that is too large to represent
    /// in the type. In such a case, this function returns `MIN` itself.    
    fn wrapping_neg(self) -> Self;

    /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping around at
    /// the boundary of the type.
    ///
    /// The only case where such wrapping can occur is when one takes the absolute value of the negative
    /// minimal value for the type; this is a positive value that is too large to represent in the type. In
    /// such a case, this function returns `MIN` itself.
    fn wrapping_abs(self) -> Self;

    // todo: (overflowing | wrapping | checked)_abs
}
