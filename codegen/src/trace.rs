use std::borrow::Cow;

use {
    proc_macro2::{Span, TokenStream},
    syn::{
        self, Data, DataEnum, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
        Generics, Ident, Type, Variant,
    },
};

use crate::{
    attr,
    shared::{map_type_params, split_for_impl},
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

    let tokens = if container.skip {
        gen_impl(&container, ident, generics, quote!())
    } else {
        match data {
            Data::Struct(ast) => derive_struct(&container, ast, ident, generics),
            Data::Enum(ast) => derive_enum(&container, ast, ident, generics),
            Data::Union(_) => panic!("Unions are not supported"),
        }
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
        Fields::Named(FieldsNamed { named, .. }) => gen_struct_cons(&ident, &named),
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => gen_tuple_struct_cons(&ident, &unnamed),
        Fields::Unit => quote! {},
    };

    gen_impl(container, ident, generics, cons)
}

fn gen_struct_cons<'a, I>(_ident: &Ident, fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
{
    let fields = fields
        .into_iter()
        .map(|field| &field.ident)
        .collect::<Vec<_>>();
    quote! {
        match self {
            Self { #(#fields),* } => {
                #(mark(#fields, gc);)*
            }
        }
    }
}

fn gen_tuple_struct_cons<'a, I>(ident: &Ident, fields: I) -> TokenStream
where
    I: IntoIterator<Item = &'a Field>,
{
    let fields = fields
        .into_iter()
        .enumerate()
        .map(|(idx, _)| Ident::new(&format!("_{}", idx), Span::call_site()))
        .collect::<Vec<_>>();
    let fields = &fields;
    quote! {
        match self {
            #ident(#(#fields,)*) => {
                #(mark(#fields, gc);)*
            }
        }
    }
}

fn derive_enum(
    container: &attr::Container,
    ast: DataEnum,
    ident: Ident,
    generics: Generics,
) -> TokenStream {
    let cons = if ast.variants.is_empty() {
        quote!()
    } else {
        let variants = ast
            .variants
            .iter()
            .map(|variant| gen_variant_match(&ident, variant));

        quote! {
            match self {
                #(#variants,)*
            }
        }
    };

    let tokens = gen_impl(container, ident, generics, cons);
    tokens
}

fn gen_impl(
    container: &attr::Container,
    ident: Ident,
    generics: Generics,
    push_impl: TokenStream,
) -> TokenStream {
    // generate bounds like T: Getable for every type parameter
    let trace_bounds = create_trace_bounds(&generics);

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[], &[]);

    let dummy_const = Ident::new(
        &format!("_IMPL_TRAVERSEABLE_FOR_{}", ident),
        Span::call_site(),
    );

    let gluon = match container.crate_name {
        attr::CrateName::Some(ref ident) => quote! {
            use #ident::gc as _gluon_gc;
        },
        attr::CrateName::GluonVm => quote! {
            use crate::gc as _gluon_gc;
        },
        attr::CrateName::None => quote! {
            use gluon::vm::gc as _gluon_gc;
        },
    };

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {
            #gluon

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            unsafe impl #impl_generics _gluon_gc::Trace for #ident #ty_generics
                #where_clause #(#trace_bounds,)*
            {
                unsafe fn root(&mut self) {
                    unsafe fn mark<T: ?Sized + _gluon_gc::Trace>(this: &mut T, _: ()) {
                        _gluon_gc::Trace::root(this)
                    }
                    let gc = ();
                    #push_impl
                }
                unsafe fn unroot(&mut self) {
                    unsafe fn mark<T: ?Sized + _gluon_gc::Trace>(this: &mut T, _: ()) {
                        _gluon_gc::Trace::unroot(this)
                    }
                    let gc = ();
                    #push_impl
                }
                fn trace(&self, gc: &mut _gluon_gc:: Gc) {
                    fn mark<T: ?Sized + _gluon_gc::Trace>(this: &T, gc: &mut _gluon_gc::Gc) {
                        _gluon_gc::Trace::trace(this, gc)
                    }
                    #push_impl
                }
            }
        };
    }
}

fn gen_variant_match(ident: &Ident, variant: &Variant) -> TokenStream {
    let (field_idents, _field_types) = get_info_from_fields(&variant.fields);
    let field_idents2 = &field_idents;
    let variant_ident = &variant.ident;

    let pattern = match &variant.fields {
        Fields::Named(_) => quote! { #ident::#variant_ident{ #( #field_idents2),* } },
        Fields::Unnamed(_) => quote! { #ident::#variant_ident( #(#field_idents2),* ) },
        Fields::Unit => quote! { #ident::#variant_ident },
    };

    quote! {
        #pattern => {
            #(mark(#field_idents2, gc);)*
        }
    }
}

fn create_trace_bounds(generics: &Generics) -> Vec<TokenStream> {
    map_type_params(generics, |ty| {
        quote! {
            #ty: _gluon_gc::Trace
        }
    })
}

fn get_info_from_fields(fields: &Fields) -> (Vec<Cow<Ident>>, Vec<&Type>) {
    // get all the fields if there are any
    let fields = match fields {
        Fields::Named(FieldsNamed { named, .. }) => named,
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => unnamed,
        Fields::Unit => return (Vec::new(), Vec::new()),
    };

    fields
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            // if the fields belong to a struct we use the field name,
            // otherwise generate one from the index of the tuple element
            let ident = match &field.ident {
                Some(ident) => Cow::Borrowed(ident),
                None => Cow::Owned(Ident::new(&format!("_{}", idx), Span::call_site())),
            };

            (ident, &field.ty)
        })
        .unzip()
}
