use proc_macro2::{Ident, Span, TokenStream};
use syn::{self, Data, DeriveInput, Generics};

use crate::{
    attr::{Container, CrateName},
    shared::{map_lifetimes, map_type_params, split_for_impl},
};

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
        quote! { #ty: 'static + ::std::fmt::Debug + _gluon_gc::Trace + Sync + Send }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[], &[]);

    let gluon = match container.crate_name {
        CrateName::Some(ref ident) => quote! {
            use #ident::api as _gluon_api;
            use #ident::gc as _gluon_gc;
            use #ident::Result as _gluon_Result;
        },
        CrateName::GluonVm => quote! {
            use crate::api as _gluon_api;
            use crate::thread as _gluon_gc;
            use crate::Result as _gluon_Result;
        },
        CrateName::None => quote! {
            use gluon::vm::api as _gluon_api;
            use gluon::vm::gc as _gluon_gc;
            use gluon::vm::Result as _gluon_Result;
        },
    };

    let dummy_const = Ident::new(&format!("_IMPL_USERDATA_FOR_{}", ident), Span::call_site());

    let deep_clone = if container.clone {
        quote! {
            fn deep_clone<'gc>(
                &self,
                deep_cloner: &'gc mut _gluon_api::Cloner
            ) -> _gluon_Result<_gluon_gc::GcRef<'gc, Box<dyn _gluon_api::Userdata>>> {
                let data: Box<dyn _gluon_api::Userdata> = Box::new(self.clone());
                deep_cloner.gc().alloc(_gluon_gc::Move(data))
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {
            #gluon

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_api::Userdata for #ident #ty_generics
            #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
            {
                #deep_clone
            }
        };
    }
}
