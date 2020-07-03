use proc_macro2::{Span, TokenStream};
use syn::{
    self, Data, DataEnum, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
    Generics, Ident, Variant,
};

use crate::{
    attr,
    shared::{map_lifetimes, map_type_params, split_for_impl},
};

pub fn derive(input: TokenStream) -> TokenStream {
    let derive_input = syn::parse2(input).expect("Input is checked by rustc");

    let container = attr::Container::from_ast(&derive_input);

    let DeriveInput {
        ident,
        data,
        generics,
        ..
    } = derive_input;

    let tokens = match data {
        Data::Struct(ast) => derive_struct(&container, ast, ident, generics),
        Data::Enum(ast) => derive_enum(&container, ast, ident, generics),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn derive_struct(
    container: &attr::Container,
    ast: DataStruct,
    ident: Ident,
    generics: Generics,
) -> TokenStream {
    let cons = match ast.fields {
        Fields::Named(FieldsNamed { named, .. }) => gen_struct_cons(&ident, named),
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => gen_tuple_struct_cons(&ident, unnamed),
        Fields::Unit => quote! { #ident },
    };

    gen_impl(container, ident, generics, cons)
}

fn gen_struct_cons<I>(ident: &Ident, fields: I) -> TokenStream
where
    I: IntoIterator<Item = Field>,
{
    // lookup each field by its name and then convert to its type using the Getable
    // impl of the fields type
    let field_initializers = fields.into_iter().map(|field| {
        let field_ty = &field.ty;
        let ident = field
            .ident
            .as_ref()
            .expect("Struct fields always have names");
        let quoted_ident = format!("{}", quote! { #ident });

        quote! {
            #ident: if let Some(val) = data.lookup_field(vm, #quoted_ident) {
                <#field_ty as _gluon_api::Getable<'__vm, '__value>>::from_value(vm, val)
            } else {
                panic!("Cannot find the field '{}'. Do the type definitions match?", #quoted_ident);
            }
        }
    });

    let unpack_data = unpack_data();
    quote! {
        #unpack_data

        #ident {
            #(#field_initializers,)*
        }
    }
}

fn gen_tuple_struct_cons<I>(ident: &Ident, fields: I) -> TokenStream
where
    I: IntoIterator<Item = Field>,
{
    let mut fields = fields.into_iter().fuse();

    // Treat newtype structs as just their inner type
    let (first, second) = (fields.next(), fields.next());
    match (&first, &second) {
        (Some(field), None) => {
            let field_ty = &field.ty;
            return quote! {
                #ident (
                <#field_ty as _gluon_api::Getable<'__vm, '__value>>::from_value(vm, variants)
                )
            };
        }
        _ => (),
    }

    // do the lookup using the tag, because tuple structs don't have field names
    let field_initializers = first
        .into_iter()
        .chain(second)
        .chain(fields)
        .enumerate()
        .map(|(tag, field)| {
            let field_ty = &field.ty;

            quote! {
                if let Some(val) = data.get_variant(#tag) {
                    <#field_ty as _gluon_api::Getable<'__vm, '__value>>::from_value(vm, val)
                } else {
                    panic!("Cannot find the field with tag '{}'. Do the type definitions match?", #tag);
                }
            }
        });

    let unpack_data = unpack_data();
    quote! {
        #unpack_data

        #ident (
            #(#field_initializers,)*
        )
    }
}

fn derive_enum(
    container: &attr::Container,
    ast: DataEnum,
    ident: Ident,
    generics: Generics,
) -> TokenStream {
    let cons;
    {
        let variants = ast
            .variants
            .iter()
            .enumerate()
            .map(|(tag, variant)| gen_variant_match(&ident, tag, variant));

        let unpack_data = unpack_data();

        // data contains the the data for each field of a variant; the variant of the passed value
        // is defined by the tag(), which is defined by order of the variants (the first variant is 0)
        cons = quote! {
            #unpack_data

            match data.tag() as usize {
                #(#variants,)*
                tag => panic!("Unexpected tag: '{}'. Do the type definitions match?", tag)
            }
        };
    }

    gen_impl(container, ident, generics, cons)
}

fn gen_impl(
    container: &attr::Container,
    ident: Ident,
    generics: Generics,
    push_impl: TokenStream,
) -> TokenStream {
    // lifetime bounds like '__vm: 'a, 'a: '__vm (which implies => 'a == '__vm)
    // writing bounds like this is a lot easier than actually replacing all lifetimes
    // with '__vm
    let lifetime_bounds = create_lifetime_bounds(&generics);

    // generate bounds like T: Getable for every type parameter
    let getable_bounds = create_getable_bounds(&generics);

    let (impl_generics, ty_generics, where_clause) =
        split_for_impl(&generics, &[], &["'__vm", "'__value"]);

    let dummy_const = Ident::new(&format!("_IMPL_GETABLE_FOR_{}", ident), Span::call_site());

    let gluon = match container.crate_name {
        attr::CrateName::Some(ref ident) => quote! {
            use #ident::api as _gluon_api;
            use #ident::thread as _gluon_thread;
            use #ident::Variants as _GluonVariants;
            use #ident::Result as _GluonResult;
        },
        attr::CrateName::GluonVm => quote! {
            use crate::api as _gluon_api;
            use crate::thread as _gluon_thread;
            use crate::Variants as _GluonVariants;
            use crate::Result as _GluonResult;
        },
        attr::CrateName::None => quote! {
            use gluon::vm::api as _gluon_api;
            use gluon::vm::thread as _gluon_thread;
            use gluon::vm::Variants as _GluonVariants;
            use gluon::vm::Result as _GluonResult;
        },
    };

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {
            #gluon

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_api::Getable<'__vm, '__value> for #ident #ty_generics
            #where_clause #(#getable_bounds,)* #(#lifetime_bounds),*
            {
                type Proxy = _GluonVariants<'__value>;

                fn to_proxy(vm: &'__vm _gluon_thread::Thread, value: _GluonVariants<'__value>) -> _GluonResult<Self::Proxy> {
                    Ok(value)
                }

                fn from_proxy(vm: &'__vm _gluon_thread::Thread, proxy: &'__value mut Self::Proxy) -> Self {
                    Self::from_value(vm, proxy.clone())
                }

                fn from_value(vm: &'__vm _gluon_thread::Thread, variants: _GluonVariants<'__value>) -> Self {
                    #push_impl
                }
            }
        };
    }
}

fn gen_variant_match(ident: &Ident, tag: usize, variant: &Variant) -> TokenStream {
    let variant_ident = &variant.ident;

    // depending on the type of the variant we need to generate different constructors
    // for the enum
    match &variant.fields {
        Fields::Unit => quote! {
            #tag => #ident::#variant_ident
        },
        // both constructors that need to marshall values extract them by using the index
        // of the field to get the content from Data::get_variant;
        // the data variable was assigned in the function body above
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => {
            let cons = gen_tuple_variant_cons(unnamed);

            quote! {
                #tag => #ident::#variant_ident#cons
            }
        }
        Fields::Named(FieldsNamed { named, .. }) => {
            let cons = gen_struct_variant_cons(ident, variant_ident, named);

            quote! {
                #tag => #cons
            }
        }
    }
}

fn gen_tuple_variant_cons<'a, I>(fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
{
    let fields = fields.into_iter().enumerate().map(|(idx, field)| {
        let field_ty = &field.ty;

        quote! {
            if let Some(val) = data.get_variant(#idx) {
                <#field_ty as _gluon_api::Getable<'__vm, '__value>>::from_value(vm, val)
            } else {
                panic!("Enum does not contain data at index '{}'. Do the type definitions match?", #idx)
            }
        }
    });

    quote! {
        (#(#fields),*)
    }
}

fn gen_struct_variant_cons<'a, I>(ident: &Ident, variant_ident: &Ident, fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
{
    let fields = fields.into_iter().map(|field| {
        let field_ty = &field.ty;
        let field_ident = field
            .ident
            .as_ref()
            .expect("Struct fields always have names");
        let quoted_field_ident = format!("{}", quote! { #field_ident });
        quote! {
            #field_ident: if let Some(val) = inner_data.lookup_field(vm, #quoted_field_ident) {
                <#field_ty as _gluon_api::Getable<'__vm, '__value>>::from_value(vm, val)
            } else {
                panic!("Enum does not contain the field `{}`. Do the type definitions match?", #quoted_field_ident)
            }
        }
    });

    quote! {{
        if let Some(val) = data.get_variant(0) {
            let inner_data = match val.as_ref() {
                _gluon_api::ValueRef::Data(data) => data,
                val => panic!("Unexpected value: '{:?}'. Do the type definitions match?", val),
            };
            #ident::#variant_ident{#(#fields),*}
        } else {
            panic!("Enum does not contain data at index '0'. Do the type definitions match?")
        }
    }}
}

fn create_getable_bounds(generics: &Generics) -> Vec<TokenStream> {
    map_type_params(generics, |ty| {
        quote! {
            #ty: _gluon_api::Getable<'__vm, '__value>
        }
    })
}

fn create_lifetime_bounds(generics: &Generics) -> Vec<TokenStream> {
    map_lifetimes(generics, |lifetime| {
        quote! { #lifetime: '__value, '__value: #lifetime }
    })
}

fn unpack_data() -> TokenStream {
    quote! {
        let data = match variants.as_ref() {
            _gluon_api::ValueRef::Data(data) => data,
            val => panic!("Unexpected value: '{:?}'. Do the type definitions match?", val),
        };
    }
}
