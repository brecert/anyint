#![feature(decl_macro)]
extern crate proc_macro;

use std::str::FromStr;

use proc_macro::TokenStream;
use proc_macro2::Literal;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, LitInt, Result};

// TODO: This whole file should be cleaned up
// TODO: figure out how macro syntax and semantics should work
// TODO: documentation

struct ParsedInt {
    digits: String,
    bits: u32,
    sign: char,
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

        let suffix = int.suffix();

        let sign = match suffix.chars().next() {
            Some(sign @ ('i' | 'u')) => sign,
            _ => return Err(input.error("Expected `i` or `u`")),
        };

        let bits = suffix
            .get(1..)
            .ok_or_else(|| input.error("No bit size specified"))?
            .parse::<u32>()
            .map_err(|err| input.error(err.to_string()))?;

        Ok(ParsedInt { digits, sign, bits })
    }
}

macro overflowing_int_error($val:expr, $bits:expr, $min:expr, $max:expr, $ty: expr) {{
    let message = format!(
        "int out of range for int size of `{1}`
the value `{0}` does not fit into the type `int<{4}, {1}>` whose range is `{2}..={3}`",
        $val,
        $bits,
        $min,
        $max,
        $ty
    );
    quote!(compile_error!(#message)).into()
}}

impl ParsedInt {
    fn is_signed(&self) -> bool {
        self.sign != 'u'
    }

    fn bit_size(&self) -> u32 {
        self.bits
            .saturating_add(1)
            .next_power_of_two()
            .clamp(8, 128)
    }

    fn max(&self) -> u128 {
        if self.is_signed() {
            (1 << self.bits.saturating_sub(1)) - 1
        } else {
            (1 << self.bits) - 1
        }
    }

    fn min(&self) -> i128 {
        if self.is_signed() {
            !(self.max() as i128)
        } else {
            0
        }
    }

    fn value<T: FromStr>(&self) -> std::result::Result<T, T::Err> {
        self.digits.parse::<T>()
    }
}

#[proc_macro]
pub fn n(input: TokenStream) -> TokenStream {
    let int = parse_macro_input!(input as ParsedInt);

    let bits = Literal::u32_unsuffixed(int.bits);

    let ty = format_ident!("{}{}", int.sign, int.bit_size());

    let val = if int.is_signed() {
        let val = int.value().unwrap();
        if val > (int.max() as i128) || val < int.min() {
            return overflowing_int_error!(int.digits, int.bits, int.min(), int.max(), ty);
        }

        Literal::i128_unsuffixed(val)
    } else {
        let val = int.value().unwrap();
        if val > int.max() {
            return overflowing_int_error!(int.digits, int.bits, int.min(), int.max(), ty);
        }

        Literal::u128_unsuffixed(val)
    };

    quote!(
        <::anyint::integer::int::<#ty, #bits>>::new(#val)
    )
    .into()
}
