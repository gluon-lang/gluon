use gluon::vm::types::VmTag;
use proc_macro2::{Span, TokenStream};
use syn::{
    self, Data, DataEnum, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    GenericParam, Generics, Ident, Lifetime, LifetimeDef, Variant,
};

pub fn derive(input: TokenStream) -> TokenStream {
    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = syn::parse2(input).expect("Input is checked by rustc");

    let tokens = match data {
        Data::Struct(ast) => derive_struct(ast, ident, generics),
        Data::Enum(ast) => derive_enum(ast, ident, generics),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn derive_struct(ast: DataStruct, ident: Ident, generics: Generics) -> TokenStream {
    // TODO: impl derive for structs
    unimplemented!()
}

fn derive_enum(ast: DataEnum, ident: Ident, generics: Generics) -> TokenStream {
    let variants: Vec<_> = ast.variants
        .iter()
        .enumerate()
        .map(|(tag, variant)| gen_variant_match(&ident, tag as VmTag, variant))
        .collect();

    let (_, ty_generics, where_clause) = generics.split_for_impl();
    let where_clause = where_clause
        .map(|clause| quote! { #clause, })
        .unwrap_or(quote! { where });

    let mut generics = generics.clone();
    let lifetime =
        GenericParam::Lifetime(LifetimeDef::new(Lifetime::new("'vm", Span::call_site())));
    generics.params.insert(0, lifetime);
    let (impl_generics, ..) = generics.split_for_impl();

    let getable_bounds = ast.variants
        .iter()
        .flat_map(|variant| create_getable_bounds(&variant.fields));

    quote! {
        impl #impl_generics ::gluon::vm::api::Getable<'vm> for #ident #ty_generics
        #where_clause #(#getable_bounds),*
        {
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

fn gen_variant_match(ident: &Ident, tag: VmTag, variant: &Variant) -> TokenStream {
    let variant_ident = &variant.ident;

    match &variant.fields {
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

fn gen_tuple_cons(fields: Vec<&Field>) -> TokenStream {
    let fields: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(idx, field)| {
            let field_ty = &field.ty;

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

fn gen_struct_cons(fields: Vec<&Field>) -> TokenStream {
    let fields: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(idx, field)| {
            let field_ty = &field.ty;
            let field_ident = field
                .ident
                .as_ref()
                .expect("Struct fields always have names");

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

fn create_getable_bounds(fields: &Fields) -> Vec<TokenStream> {
    let fields = match fields {
        Fields::Named(FieldsNamed { named, .. }) => named.iter().collect(),
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => unnamed.iter().collect(),
        Fields::Unit => Vec::new(),
    };

    fields
        .into_iter()
        .map(|field| {
            let ty = &field.ty;

            quote! {
                #ty: ::gluon::vm::api::Getable<'vm>
            }
        })
        .collect()
}
