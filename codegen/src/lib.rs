#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;
extern crate gluon;
extern crate syn;

mod getable;

#[proc_macro_derive(Getable)]
pub fn getable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    getable::derive(input.into()).into()
}
