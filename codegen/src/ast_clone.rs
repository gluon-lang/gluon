use std::str::FromStr;

use {
    proc_macro2::{Span, TokenStream},
    syn::{
        self, Data, DataEnum, DataStruct, DeriveInput, Field, Fields, FieldsNamed, FieldsUnnamed,
        Generics, Ident, Variant,
    },
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

        quote! {
            #ident: <#field_ty as gluon_base::ast::AstClone<'ast, Id>>::ast_clone(&self.#ident, arena)
        }
    });

    quote! {

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
                    <#field_ty as gluon_base::ast::AstClone<'__vm, _>>::ast_clone(&self.0, arena)
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
        .map(|(idx, field)| {
            let field_ty = &field.ty;
            let idx = syn::Index::from(idx);

            quote! {
                <#field_ty as gluon_base::ast::AstClone<'__vm, _>>::ast_clone(&self. #idx, arena)
            }
        });

    quote! {

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
    let cons = {
        let variants = ast
            .variants
            .iter()
            .enumerate()
            .map(|(tag, variant)| gen_variant_match(&ident, tag, variant));

        // data contains the the data for each field of a variant; the variant of the passed value
        // is defined by the tag(), which is defined by order of the variants (the first variant is 0)
        quote! {
            match self {
                #(#variants,)*
            }
        }
    };

    gen_impl(container, ident, generics, cons)
}

fn gen_impl(
    container: &attr::Container,
    ident: Ident,
    generics: Generics,
    clone_impl: TokenStream,
) -> TokenStream {
    // lifetime bounds like '__vm: 'a, 'a: '__vm (which implies => 'a == '__vm)
    // writing bounds like this is a lot easier than actually replacing all lifetimes
    // with '__vm
    let lifetime_bounds = create_lifetime_bounds(&generics);

    // generate bounds like T: Getable for every type parameter
    let ast_clone_bounds = create_ast_clone_bounds(&generics);

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &["Id"], &["'ast"]);

    let dummy_const = Ident::new(&format!("_IMPL_AST_CLONE_FOR_{}", ident), Span::call_site());

    let extra_bounds = container.ast_clone_bounds.as_ref().map(|b| {
        let b = TokenStream::from_str(b).unwrap();
        quote! { #b, }
    });

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {
            use crate as gluon_base;

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics gluon_base::ast::AstClone<'ast, Id> for #ident #ty_generics
                #where_clause #(#ast_clone_bounds,)* #(#lifetime_bounds),* #extra_bounds Id: Clone
            {
                fn ast_clone(&self, arena: gluon_base::ast::ArenaRef<'_, 'ast, Id>) -> Self {
                    #clone_impl
                }
            }
        };
    }
}

fn gen_variant_match(ident: &Ident, _tag: usize, variant: &Variant) -> TokenStream {
    let variant_ident = &variant.ident;

    // depending on the type of the variant we need to generate different constructors
    // for the enum
    match &variant.fields {
        Fields::Unit => quote! {
            #ident::#variant_ident => #ident::#variant_ident
        },
        // both constructors that need to marshall values extract them by using the index
        // of the field to get the content from Data::get_variant;
        // the data variable was assigned in the function body above
        Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => {
            let fields: Vec<_> = unnamed
                .iter()
                .enumerate()
                .map(|(idx, _field)| syn::Ident::new(&format!("_{}", idx), Span::call_site()))
                .collect();
            let cons = gen_tuple_variant_cons(unnamed.iter().zip(fields.iter()));

            quote! {
                #ident::#variant_ident ( #(#fields),* ) =>
                    #ident::#variant_ident#cons
            }
        }
        Fields::Named(FieldsNamed { named, .. }) => {
            let cons = gen_struct_variant_cons(ident, variant_ident, named);
            let named = named.iter().map(|field| field.ident.as_ref().unwrap());

            quote! {
                #ident::#variant_ident { #(#named),* } => #cons
            }
        }
    }
}

fn gen_tuple_variant_cons<'a, I>(fields: I) -> TokenStream
where
    I: IntoIterator<Item = (&'a syn::Field, &'a syn::Ident)>,
{
    let fields = fields.into_iter().map(|(field, ident)| {
        let field_ty = &field.ty;

        quote! {
            <#field_ty as gluon_base::ast::AstClone<_>>::ast_clone(#ident, arena)
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
        quote! {
            #field_ident: <#field_ty as gluon_base::ast::AstClone<_>>::ast_clone(#field_ident, arena)
        }
    });

    quote! {
        #ident::#variant_ident { #(#fields),* }
    }
}

fn create_ast_clone_bounds(generics: &Generics) -> Vec<TokenStream> {
    map_type_params(generics, |ty| {
        quote! {
            #ty: gluon_base::ast::AstClone<'ast, Id>
        }
    })
}

fn create_lifetime_bounds(generics: &Generics) -> Vec<TokenStream> {
    map_lifetimes(generics, |_lifetime| {
        quote! {}
    })
}
