use proc_macro2::{Ident, TokenStream};
use shared::{map_lifetimes, map_type_params, split_for_impl};
use syn::{self, Data, DeriveInput, Fields, GenericParam, Generics};

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
        Data::Struct(_) | Data::Enum(_) => gen_impl(&container, ident, generics, &data),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(container: &Container, ident: Ident, generics: Generics, data: &Data) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: ::gluon::vm::api::VmType, #ty::Type: Sized }
    });

    let lifetime_bounds = &map_lifetimes(&generics, |lifetime| quote! { #lifetime: 'static });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[]);

    let make_type_impl = match container.vm_type {
        Some(ref gluon_type) => {
            let type_application = gen_type_application(&generics);
            quote!{
                let ty = match vm.find_type_info(#gluon_type) {
                    Ok(info) => info.into_type(),
                    Err(_) => panic!("Could not find type '{}'. Is the module defining the type loaded?", #gluon_type),
                };

                #type_application
            }
        }
        None => match *data {
            Data::Struct(ref struct_) => match struct_.fields {
                Fields::Named(ref fields) => {
                    let fields = fields.named.iter().map(|field| {
                        let ident = field.ident.as_ref().unwrap().to_string();
                        let typ = &field.ty;
                        quote! {
                            ::gluon::base::types::Field {
                                name: ::gluon::base::symbol::Symbol::from(#ident),
                                typ: <#typ as ::gluon::vm::api::VmType>::make_type(vm),
                            }
                        }
                    });
                    quote!{
                        ::gluon::base::types::Type::record(
                            vec![],
                            vec![#(#fields),*],
                        )
                    }
                }
                Fields::Unnamed(ref fields) => {
                    if fields.unnamed.len() == 1 {
                        let typ = &fields.unnamed[0].ty;
                        quote!{
                            <#typ as ::gluon::vm::api::VmType>::make_type(vm)
                        }
                    } else {
                        let fields = fields.unnamed.iter().map(|field| &field.ty);
                        quote!{
                            ::gluon::base::types::Type::tuple(vec![#(
                                <#fields as ::gluon::vm::api::VmType>::make_type(vm)
                            ),*])
                        }
                    }
                }
                Fields::Unit => quote!(::gluon::base::types::Type::unit()),
            },
            _ => panic!("Only structs can derive `VmType` without using the `vm_type` attribute"),
        },
    };

    let associated_type_generics = generics.params.iter().map(|param| match param {
        GenericParam::Type(ty) => quote!( #ty :: Type ),
        GenericParam::Lifetime(lt) => quote!( #lt ),
        GenericParam::Const(c) => quote!( #c ),
    });

    quote! {
        #[automatically_derived]
        #[allow(unused_attributes, unused_variables)]
        impl #impl_generics ::gluon::vm::api::VmType for #ident #ty_generics
        #where_clause #(#trait_bounds,)* #(#lifetime_bounds),*
        {
            type Type = #ident<
                    #(#associated_type_generics),*
                >;

            fn make_type(vm: &::gluon::vm::thread::Thread) -> ::gluon::base::types::ArcType {
                #make_type_impl
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
