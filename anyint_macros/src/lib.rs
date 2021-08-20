extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Literal;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, LitInt, Result};

struct IntType {
    digits: String,
    bits: u32,
    sign: char,
}

impl Parse for IntType {
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
            digits.insert_str(0, "-")
        }

        let suffix = int.suffix();

        let sign = match suffix.chars().next() {
            Some(sign @ ('i' | 'u')) => sign,
            _ => return Err(input.error("Expected `i` or `u`")),
        };

        let bits = suffix
            .get(1..)
            .ok_or(input.error("No bit size specified"))?
            .parse::<u32>()
            .map_err(|err| input.error(err.to_string()))?;

        // let sign = input.parse::<IntTypeToken>()?;
        // let bits = input.parse::<LitInt>()?.base10_parse()?;

        Ok(IntType { digits, sign, bits })
    }
}

#[proc_macro]
pub fn n(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as IntType);

    let val = match input.sign {
        'i' => Literal::i128_unsuffixed(input.digits.parse::<i128>().unwrap()),
        'u' => Literal::u128_unsuffixed(input.digits.parse::<u128>().unwrap()),
        _ => unreachable!(),
    };

    let bits = Literal::u32_unsuffixed(input.bits);

    let ty = format_ident!(
        "{}{}",
        input.sign,
        input
            .bits
            .saturating_add(1)
            .next_power_of_two()
            .clamp(8, 64)
    );

    quote!(
        <int::<#ty, #bits>>::from_lossy(#val)
    )
    .into()
}
