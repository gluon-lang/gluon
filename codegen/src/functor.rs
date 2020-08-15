extern crate proc_macro;

use proc_macro2::{Ident, Span, TokenStream};
use syn::{self, Data, DeriveInput, Generics};

use crate::shared::split_for_impl;

pub fn derive(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse2(input).expect("Input is checked by rustc");

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derive_input;

    let tokens = match data {
        Data::Struct(_) | Data::Enum(_) => gen_impl(ident, generics, &data),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(ident: Ident, generics: Generics, data: &Data) -> TokenStream {
    assert!(generics.type_params().count() > 0);
    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[], &[]);

    let map_methods = generics
        .type_params()
        .last()
        .map(|gen| gen_map(&ident, &generics, &gen.ident, data))
        .into_iter();

    quote! {
        impl #impl_generics #ident #ty_generics
            #where_clause
        {

            #(#map_methods)*
        }
    }
}

fn gen_map(ident: &Ident, generics: &Generics, param: &syn::Ident, data: &Data) -> TokenStream {
    let replaced_ident = syn::Ident::new("RET", Span::call_site());
    let mut new_generics = generics.clone();
    new_generics.type_params_mut().for_each(|type_param| {
        if type_param.ident == *param {
            type_param.ident = replaced_ident.clone();
        }
    });

    let map_ident = syn::Ident::new(
        &format!("map_{}", param.to_string().to_ascii_lowercase()),
        Span::call_site(),
    );

    let mut bounds = Vec::new();
    let map_expr = match data {
        syn::Data::Enum(data) => gen_map_expr(&ident, &map_ident, param, data, &mut bounds),
        syn::Data::Struct(data) => {
            let (unpack, pack) = gen_field_packing(&map_ident, param, &data.fields, &mut bounds);
            quote! {
                match self {
                    #ident #unpack => #ident #pack
                }
            }
        }
        _ => unimplemented!("Non-enum data"),
    };

    quote! {
        pub fn #map_ident<RET>(self, __f: &mut impl FnMut( #param ) -> RET) -> #ident #new_generics
            where #param: Clone
        {
            #map_expr
        }
    }
}

fn gen_map_expr(
    enum_ident: &Ident,
    map_ident: &syn::Ident,
    param: &syn::Ident,
    data: &syn::DataEnum,
    bounds: &mut Vec<syn::Ident>,
) -> TokenStream {
    let variants = data.variants.iter().map(|variant| {
        let variant_ident = &variant.ident;
        let (unpack, pack) = gen_field_packing(map_ident, param, &variant.fields, bounds);
        quote! {
            #enum_ident :: #variant_ident #unpack => {
                #enum_ident :: #variant_ident #pack
            }
        }
    });
    quote! {
        match self {
            #(#variants),*
        }
    }
}

enum Container {
    Vec,
    List,
}

enum Parameter {
    Direct,
    Indirect,
    InContainer(Container, Box<Parameter>),
}

fn detect_parameter(typ: &syn::Type, param: &syn::Ident) -> Option<Parameter> {
    match typ {
        syn::Type::Path(ref p) => {
            if p.qself.is_none() && p.path.is_ident(param) {
                Some(Parameter::Direct)
            } else {
                p.path.segments.iter().find_map(|segment| {
                    let mut is_vec = false;
                    let mut is_list = false;
                    if segment.ident == "Vec" {
                        is_vec = true;
                    }
                    if segment.ident == "List" || segment.ident == "ListSync" {
                        is_list = true;
                    }
                    match &segment.arguments {
                        syn::PathArguments::AngleBracketed(arguments) => arguments
                            .args
                            .iter()
                            .find_map(|arg| match arg {
                                syn::GenericArgument::Type(typ) => detect_parameter(typ, param),
                                _ => None,
                            })
                            .map(|parameter| {
                                if is_vec {
                                    Parameter::InContainer(Container::Vec, Box::new(parameter))
                                } else if is_list {
                                    Parameter::InContainer(Container::List, Box::new(parameter))
                                } else {
                                    Parameter::Indirect
                                }
                            }),
                        _ => None,
                    }
                })
            }
        }
        _ => None,
    }
}

fn quote_parameter(
    param: &Parameter,
    map_ident: &syn::Ident,
    id: &syn::Ident,
    bounds: &mut Vec<syn::Ident>,
) -> TokenStream {
    match param {
        Parameter::Direct => quote!(__f(#id)),
        Parameter::Indirect => quote!(#id . #map_ident(__f)),
        Parameter::InContainer(container, param) => {
            let inner = quote_parameter(
                param,
                map_ident,
                &syn::Ident::new("e", Span::call_site()),
                bounds,
            );
            match container {
                Container::Vec => quote!(#id.into_iter().map(|e| #inner).collect()),
                Container::List => {
                    bounds.push(syn::Ident::new("Clone", Span::call_site()));
                    quote!(#id.into_iter().map(|e| { let e = e.clone(); #inner }).collect())
                }
            }
        }
    }
}

fn gen_field_packing(
    map_ident: &syn::Ident,
    param: &syn::Ident,
    fields: &syn::Fields,
    bounds: &mut Vec<syn::Ident>,
) -> (TokenStream, TokenStream) {
    let mut pack_ident =
        |id: &syn::Ident, field: &syn::Field| match detect_parameter(&field.ty, param) {
            None => quote!(#id),
            Some(parameter) => quote_parameter(&parameter, map_ident, id, bounds),
        };

    match fields {
        syn::Fields::Unnamed(unnamed) => {
            let variables = unnamed
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, _)| syn::Ident::new(&format!("_{}", i), Span::call_site()))
                .collect::<Vec<_>>();
            let unpacks = variables.iter();
            let packs = variables
                .iter()
                .zip(&unnamed.unnamed)
                .map(|(id, field)| pack_ident(id, field));
            (
                quote! {
                    ( #(#unpacks),* )
                },
                quote! {
                    ( #(#packs),* )
                },
            )
        }
        syn::Fields::Named(named) => {
            let unpacks = named.named.iter().map(|field| &field.ident);
            let packs = named.named.iter().map(|field| {
                let id = &field.ident.as_ref().unwrap();
                let pack = pack_ident(id, field);
                quote! { #id : #pack }
            });
            (
                quote! {
                    { #(#unpacks),* }
                },
                quote! {
                    { #(#packs),* }
                },
            )
        }
        syn::Fields::Unit => (quote!(), quote!()),
    }
}
