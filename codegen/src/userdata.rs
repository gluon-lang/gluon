use proc_macro2::{Ident, Span, TokenStream};
use shared::{map_lifetimes, map_type_params, split_for_impl};
use syn::{self, Data, DeriveInput, GenericParam, Generics};

use attr::{Container, CrateName};

pub fn derive(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse2(input).expect("Input is checked by rustc");

    let container = Container::from_ast(&derive_input);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derive_input;

    let tokens = match data {
        Data::Struct(_) | Data::Enum(_) => gen_impl(&container, ident, generics),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(container: &Container, ident: Ident, generics: Generics) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: 'static + ::std::fmt::Debug + Sync + Send }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    let gluon = match container.crate_name {
        CrateName::Some(ref ident) => quote!{
            use #ident::api as _gluon_api;
            use #ident::gc as _gluon_gc;
        },
        CrateName::GluonVm => quote!{
            use api as _gluon_api;
            use thread as _gluon_gc;
        },
        CrateName::None => quote!{
            use gluon::vm::api as _gluon_api;
            use gluon::vm::gc as _gluon_gc;
        },
    };

    let associated_type_generics = generics.params.iter().map(|param| match param {
        GenericParam::Type(ty) => quote!( #ty :: Type ),
        GenericParam::Lifetime(_) => quote!( 'static ),
        GenericParam::Const(c) => quote!( #c ),
    });

    let dummy_const = Ident::new(&format!("_IMPL_USERDATA_FOR_{}", ident), Span::call_site());

    quote! {
        const #dummy_const: () = {
            #gluon

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_api::Userdata for #ident #ty_generics
            #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
            {
            }

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_gc::Traverseable for #ident #ty_generics {}

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_api::VmType for #ident #ty_generics
            #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
            {
                type Type = #ident<
                        #(#associated_type_generics),*
                    >;
            }
        };
    }
}
