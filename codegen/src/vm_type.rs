use proc_macro2::{Ident, TokenStream};
use shared::{map_lifetimes, map_type_params, split_for_impl};
use syn::{
    self, Attribute, Data, DeriveInput, Generics, Lit, Meta, MetaList, MetaNameValue, NestedMeta,
};

pub fn derive(input: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        attrs,
        data,
        generics,
        ..
    } = syn::parse2(input).expect("Input is checked by rustc");

    let tokens = match data {
        Data::Struct(_) | Data::Enum(_) => gen_impl(ident, generics, &parse_attrs(&attrs)),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn parse_attrs(attrs: &[Attribute]) -> String {
    let ty = attrs
        .iter()
        .filter_map(|attr| {
            attr.interpret_meta().and_then(|meta| {
                // all attrs are namespaced under the gluon attr
                let nested = match meta {
                    Meta::List(MetaList {
                        ref ident,
                        ref nested,
                        ..
                    }) if ident == "gluon" =>
                    {
                        Some(nested)
                    }
                    _ => None,
                }?;

                // find a literal for the vm_type key, ignore other values as they may be required
                // by other macros
                let lit = nested
                    .iter()
                    .filter_map(|meta| match meta {
                        NestedMeta::Meta(Meta::NameValue(MetaNameValue { ident, lit, .. }))
                            if ident == "vm_type" =>
                        {
                            Some(lit)
                        }
                        _ => None,
                    })
                    .next()?;

                match lit {
                    Lit::Str(ty) => Some(ty.value()),
                    _ => panic!("The gluon type name must be a string literal"),
                }
            })
        })
        .next();

    match ty {
        Some(ty) => ty,
        None => panic!("Did not find the gluon type this type will be mapped to. Specify it with #[gluon(vm_type = \"<gluon_type>\")]"),
    }
}

fn gen_impl(ident: Ident, generics: Generics, gluon_type: &str) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: 'static + ::gluon::vm::api::VmType }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let type_application = gen_type_application(&generics);
    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    quote! {
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
