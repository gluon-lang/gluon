extern crate proc_macro;
#[macro_use]
extern crate quote;
extern crate gluon;
extern crate syn;

mod getable;

use proc_macro::TokenStream;

#[proc_macro_derive(Getable)]
pub fn getable(input: TokenStream) -> TokenStream {
    getable::derive(input)
}
