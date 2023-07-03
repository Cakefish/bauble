use bauble_macro_util::derive_bauble;
use proc_macro::TokenStream;

// Derive `FromBauble`
#[proc_macro_derive(FromBauble, attributes(bauble))]
pub fn derive(input: TokenStream) -> TokenStream {
    derive_bauble(input.into()).into()
}
