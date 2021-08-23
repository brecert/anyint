#![feature(decl_macro)]
extern crate proc_macro;

use std::num::ParseIntError;
use std::str::FromStr;
use thiserror::Error;

use proc_macro::TokenStream;
use proc_macro2::{Ident, Literal, Span};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, LitInt, Result};

// TODO: This whole file should be cleaned up
// TODO: figure out how macro syntax and semantics should work
// TODO: documentation

enum IntType {
    Signed(u32),
    Unsigned(u32),
}

impl IntType {
    fn is_signed(&self) -> bool {
        matches!(self, Self::Signed(_))
    }

    fn bits(&self) -> u32 {
        match self {
            Self::Signed(bits) | Self::Unsigned(bits) => *bits,
        }
    }
}

impl ToString for IntType {
    fn to_string(&self) -> String {
        match self {
            Self::Signed(bits) => format!("i{}", bits),
            Self::Unsigned(bits) => format!("i{}", bits),
        }
    }
}

#[derive(Error, Debug)]
enum IntTypeParseError {
    #[error(
        "invalid suffix `{0}` for int\nthe suffix must match the pattern of `i21`, `u7`, etc.."
    )]
    InvalidSuffix(String),

    #[error("suffix is required for int")]
    NoSuffixFound,

    #[error("no bit size was specified")]
    NoBitSizeSpecified,

    #[error("invalid width for for int\n{0}")]
    InvalidSize(#[from] ParseIntError),
}

impl FromStr for IntType {
    type Err = IntTypeParseError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let first_char = s.chars().next().ok_or(IntTypeParseError::NoSuffixFound)?;
        let signed = matches!(first_char, 'i' | 'u')
            .then(|| first_char == 'i')
            .ok_or_else(|| IntTypeParseError::InvalidSuffix(s.to_string()))?;

        let size: u32 = s
            .get(1..)
            .ok_or(IntTypeParseError::NoBitSizeSpecified)?
            .parse()?;

        Ok(match signed {
            true => IntType::Signed(size),
            false => IntType::Unsigned(size),
        })
    }
}
struct ParsedInt {
    digits: String,
    ty: IntType,
}

impl Parse for ParsedInt {
    fn parse(input: ParseStream) -> Result<Self> {
        let neg = input
            .step(|cursor| {
                if let Some((punct, rest)) = cursor.punct() {
                    if punct.as_char() == '-' {
                        return Ok((true, rest));
                    }
                }

                Err(cursor.error("Integer literal expected"))
            })
            .unwrap_or_default();

        let int = input.parse::<LitInt>()?;

        let mut digits = int.base10_digits().to_string();

        if neg {
            digits.insert(0, '-')
        }

        let ty: IntType = int
            .suffix()
            .parse()
            .map_err(|err: IntTypeParseError| input.error(err.to_string()))?;

        if ty.bits() > 127 {
            return Err(input.error(format!(
                "int width out of range at `{0}`\nthe int width `{0}` does not fit into the range of `0..=127`",
                ty.bits()
            )));
        }

        Ok(ParsedInt { digits, ty })
    }
}

macro overflowing_int_error($val:expr, $bits:expr, $min:expr, $max:expr, $ty: expr) {{
    let message = format!(
        "int out of range for int width of `{1}`
the value `{0}` does not fit into the type `int<{4}, {1}>` whose range is `{2}..={3}`",
        $val, $bits, $min, $max, $ty
    );
    quote!(compile_error!(#message)).into()
}}

impl ParsedInt {
    fn bit_size(&self) -> u32 {
        self.ty
            .bits()
            .saturating_add(1)
            .next_power_of_two()
            .clamp(8, 128)
    }

    fn max(&self) -> u128 {
        if self.ty.is_signed() {
            (1 << self.ty.bits().saturating_sub(1)) - 1
        } else {
            (1 << self.ty.bits()) - 1
        }
    }

    fn min(&self) -> i128 {
        if self.ty.is_signed() {
            !(self.max() as i128)
        } else {
            0
        }
    }

    fn value<T: FromStr>(&self) -> std::result::Result<T, T::Err> {
        self.digits.parse::<T>()
    }
}

impl ToString for ParsedInt {
    fn to_string(&self) -> String {
        format!(
            "{}{}",
            if self.ty.is_signed() { 'i' } else { 'u' },
            self.bit_size()
        )
    }
}

#[proc_macro]
pub fn n(input: TokenStream) -> TokenStream {
    let int = parse_macro_input!(input as ParsedInt);

    let bits = Literal::u32_unsuffixed(int.ty.bits());
    let ty = Ident::new(&int.to_string(), Span::call_site());

    let val = if int.ty.is_signed() {
        let val = int.value().unwrap();
        if val > (int.max() as i128) || val < int.min() {
            return overflowing_int_error!(int.digits, int.ty.bits(), int.min(), int.max(), ty);
        }

        Literal::i128_unsuffixed(val)
    } else {
        let val = int.value().unwrap();
        if val > int.max() {
            return overflowing_int_error!(int.digits, int.ty.bits(), int.min(), int.max(), ty);
        }

        Literal::u128_unsuffixed(val)
    };

    quote!(
        <::anyint::integer::int::<#ty, #bits>>::new(#val)
    )
    .into()
}
