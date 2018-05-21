use gluon::vm::types::VmTag;
use proc_macro::TokenStream;
use quote;
use syn::{
    self, Data, DataEnum, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    Ident, Variant,
};

pub fn derive(input: TokenStream) -> TokenStream {
    let DeriveInput { ident, data, .. } = syn::parse(input).expect("Input is checked by rustc");

    let tokens = match data {
        Data::Struct(ast) => derive_struct(ast, ident),
        Data::Enum(ast) => derive_enum(ast, ident),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn derive_struct(ast: DataStruct, ident: Ident) -> quote::Tokens {
    // TODO: impl derive for structs
    unimplemented!()
}

fn derive_enum(ast: DataEnum, ident: Ident) -> quote::Tokens {
    let variants: Vec<_> = ast.variants
        .into_iter()
        .enumerate()
        .map(|(tag, variant)| gen_variant_match(ident, tag as VmTag, variant))
        .collect();

    quote! {
        impl<'vm> ::gluon::vm::api::Getable<'vm> for #ident {
            fn from_value(vm: &'vm ::gluon::vm::thread::Thread, variants: ::gluon::vm::Variants) -> Self {
                let data = match variants.as_ref() {
                    ::gluon::vm::api::ValueRef::Data(data) => data,
                    val => panic!("Unexpected value: '{:?}'. Do the type definitions match?", val),
                };

                match data.tag() {
                    #(#variants,)*
                    tag => panic!("Unexpected tag: '{}'. Do the type definitions match?", tag)
                }
            }
        }
    }
}

fn gen_variant_match(ident: Ident, tag: VmTag, variant: Variant) -> quote::Tokens {
    let variant_ident = variant.ident;

    match variant.fields {
        Fields::Unit => quote! {
            #tag => #ident::#variant_ident
        },
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => {
            let cons = gen_tuple_cons(unnamed.into_iter().collect());

            quote! {
                #tag => #ident::#variant_ident#cons
            }
        }
        Fields::Named(FieldsNamed { named, .. }) => {
            let cons = gen_struct_cons(named.into_iter().collect());

            quote! {
                #tag => #ident::#variant_ident#cons
            }
        }
    }
}

fn gen_tuple_cons(fields: Vec<Field>) -> quote::Tokens {
    let fields: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(idx, field)| {
            let field_ty = field.ty;

            quote! {
                if let Some(val) = data.get_variant(#idx) {
                    <#field_ty as ::gluon::vm::api::Getable<'vm>>::from_value(vm, val)
                } else {
                    panic!("Enum does not contain data at index '{}'. Do the type definitions match?", #idx)
                }
            }
        })
        .collect();

    quote!{
        (#(#fields),*)
    }
}

fn gen_struct_cons(fields: Vec<Field>) -> quote::Tokens {
    let fields: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(idx, field)| {
            let field_ty = field.ty;
            let field_ident = field.ident.expect("Struct fields always have names");

            quote! {
                #field_ident: if let Some(val) = data.get_variant(#idx) {
                    <#field_ty as ::gluon::vm::api::Getable<'vm>>::from_value(vm, val)
                } else {
                    panic!("Enum does not contain data at index '{}'. Do the type definitions match?", #idx)
                }
            }
        })
        .collect();

    quote!{
        {#(#fields),*}
    }
}
