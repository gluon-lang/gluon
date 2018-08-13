use proc_macro2::{Ident, TokenStream};
use shared::{map_lifetimes, map_type_params, split_for_impl};
use syn::{self, Data, DeriveInput, Generics};

use attr::Container;

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
        quote! { #ty: 'static + ::gluon::vm::api::VmType }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let type_application = gen_type_application(&generics);
    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    let gluon_type = container.vm_type.as_ref().unwrap_or_else(|| {
        panic!("Did not find the gluon type this type will be mapped to. Specify it with #[gluon(vm_type = \"<gluon_type>\")]")
    });

    quote! {
        #[automatically_derived]
        #[allow(unused_attributes, unused_variables)]
        impl #impl_generics ::gluon::vm::api::VmType for #ident #ty_generics
        #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
        {
            type Type = Self;

            fn make_type(vm: &::gluon::vm::thread::Thread) -> ::gluon::base::types::ArcType {
                let ty = match vm.find_type_info(#gluon_type) {
                    Ok(info) => info.into_type(),
                    Err(_) => panic!("Could not find type '{}'. Is the module defining the type loaded?", #gluon_type),
                };

                #type_application
            }
        }
    }
}

fn gen_type_application(generics: &Generics) -> TokenStream {
    let applications = map_type_params(generics, |param| {
        quote! {
            vec.push(<#param as ::gluon::vm::api::VmType>::make_type(vm));
        }
    });

    // if there are generic parameters, we use their types and apply them
    // to the type of the derive target to construct the concrete type
    if applications.is_empty() {
        quote! {
            ty
        }
    } else {
        quote! {
            let mut vec = ::gluon::base::types::AppVec::new();
            #(#applications)*
            ::gluon::base::types::Type::app(ty, vec)
        }
    }
}
