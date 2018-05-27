#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro2;
#[macro_use]
extern crate quote;
extern crate syn;

mod getable;
mod pushable;
mod shared;
mod userdata;
mod vm_type;

#[proc_macro_derive(Getable)]
pub fn getable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    getable::derive(input.into()).into()
}

#[proc_macro_derive(Pushable)]
pub fn pushable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    pushable::derive(input.into()).into()
}

#[proc_macro_derive(Userdata)]
pub fn userdata(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    userdata::derive(input.into()).into()
}

#[proc_macro_derive(VmType, attributes(gluon))]
pub fn vm_type(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    vm_type::derive(input.into()).into()
}
