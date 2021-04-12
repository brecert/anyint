use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn n(input: TokenStream) -> TokenStream {
    let x = input.to_string();
    // todo: logic
    quote!(
        int::<i32, 31>
    ).into()
}
