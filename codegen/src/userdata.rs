use proc_macro2::{Ident, TokenStream};
use shared::{map_lifetimes, map_type_params, split_for_impl};
use syn::{self, Data, DeriveInput, Generics};

pub fn derive(input: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = syn::parse2(input).expect("Input is checked by rustc");

    let tokens = match data {
        Data::Struct(_) | Data::Enum(_) => gen_impl(ident, generics),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(ident: Ident, generics: Generics) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: 'static + ::std::fmt::Debug + Sync + Send }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    quote! {
        impl #impl_generics ::gluon::vm::api::Userdata for #ident #ty_generics
        #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
        {
        }

        impl #impl_generics ::gluon::vm::gc::Traverseable for #ident #ty_generics {}

        impl #impl_generics ::gluon::vm::api::VmType for #ident #ty_generics
        #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
        {
            type Type = Self;
        }
    }
}
