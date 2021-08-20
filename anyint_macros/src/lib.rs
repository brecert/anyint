extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Ident, Literal, Span};
use quote::{format_ident, quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Error, LitInt, Result};

mod token {
    syn::custom_keyword!(i);
    syn::custom_keyword!(u);
}

enum IntTypeToken {
    Signed,
    Unsigned,
}

impl IntTypeToken {
    fn value(self) -> char {
        match self {
            Self::Signed => 'i',
            Self::Unsigned => 'u',
        }
    }
}

impl Parse for IntTypeToken {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(token::i) {
            Ok(IntTypeToken::Signed)
        } else if lookahead.peek(token::u) {
            Ok(IntTypeToken::Unsigned)
        } else {
            Err(lookahead.error())
        }
    }
}

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
                    return Ok((punct.as_char() == '-', rest));
                }

                Err(cursor.error("message"))
            })
            .unwrap_or(false);

        let int = input.parse::<LitInt>()?;
        let suffix = int.suffix();

        let mut digits = int.base10_digits().to_string();

        if neg {
            digits.insert_str(0, "-")
        }

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
