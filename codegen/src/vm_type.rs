use proc_macro2::{Ident, Span, TokenStream};
use syn::{self, Data, DeriveInput, Fields, GenericParam, Generics};

use crate::{
    attr::{Container, CrateName},
    shared::{map_type_params, split_for_impl},
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
        Data::Struct(_) | Data::Enum(_) => gen_impl(&container, ident, generics, &data),
        Data::Union(_) => panic!("Unions are not supported"),
    };

    tokens.into()
}

fn gen_impl(container: &Container, ident: Ident, generics: Generics, data: &Data) -> TokenStream {
    let trait_bounds = &map_type_params(&generics, |ty| {
        quote! { #ty: _gluon_api::VmType, #ty::Type: Sized }
    });

    let (impl_generics, ty_generics, where_clause) = split_for_impl(&generics, &[], &[]);

    let gluon = match container.crate_name {
        CrateName::Some(ref ident) => quote! {
            use #ident::base as _gluon_base;
            use #ident::api as _gluon_api;
            use #ident::thread as _gluon_thread;
        },
        CrateName::GluonVm => quote! {
            use crate::base as _gluon_base;
            use crate::api as _gluon_api;
            use crate::thread as _gluon_thread;
        },
        CrateName::None => quote! {
            use gluon::base as _gluon_base;
            use gluon::vm::api as _gluon_api;
            use gluon::vm::thread as _gluon_thread;
        },
    };

    let make_type_impl = match container.vm_type {
        Some(ref gluon_type) => {
            let type_application = gen_type_application(&generics);
            quote! {
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
                            _gluon_base::types::Field {
                                name: _gluon_base::symbol::Symbol::from(#ident),
                                typ: <#typ as _gluon_api::VmType>::make_type(vm),
                            }
                        }
                    });
                    quote! {
                        _gluon_base::types::Type::record(
                            vec![],
                            vec![#(#fields),*],
                        )
                    }
                }
                Fields::Unnamed(ref fields) => {
                    if fields.unnamed.len() == 1 {
                        let typ = &fields.unnamed[0].ty;
                        quote! {
                            <#typ as _gluon_api::VmType>::make_type(vm)
                        }
                    } else {
                        let fields = fields.unnamed.iter().map(|field| &field.ty);
                        quote! {
                            _gluon_base::types::Type::tuple(vec![#(
                                <#fields as _gluon_api::VmType>::make_type(vm)
                            ),*])
                        }
                    }
                }
                Fields::Unit => quote!(_gluon_base::types::Type::unit()),
            },
            Data::Enum(ref enum_) => {
                let variants = enum_.variants.iter().map(|variant| {
                    let ident = variant.ident.to_string();
                    match variant.fields {
                        Fields::Named(ref fields) => {
                            let fields = fields.named.iter().map(|field| {
                                let ident = field.ident.as_ref().unwrap().to_string();
                                let typ = &field.ty;
                                quote! {
                                    _gluon_base::types::Field {
                                        name: _gluon_base::symbol::Symbol::from(#ident),
                                        typ: <#typ as _gluon_api::VmType>::make_type(vm),
                                    }
                                }
                            });
                            quote! {{
                                let ctor_name = _gluon_base::symbol::Symbol::from(#ident);
                                let typ = _gluon_base::types::Type::record(
                                    vec![],
                                    vec![#(#fields),*],
                                );
                                _gluon_base::types::Field::ctor(
                                    ctor_name,
                                    vec![typ],
                                )
                            }}
                        }
                        Fields::Unnamed(ref fields) => {
                            let args = fields.unnamed.iter().map(|field| {
                                let typ = &field.ty;
                                quote! {
                                    <#typ as _gluon_api::VmType>::make_type(vm)
                                }
                            });
                            quote! {{
                                let ctor_name = _gluon_base::symbol::Symbol::from(#ident);
                                _gluon_base::types::Field::ctor(
                                    ctor_name,
                                    vec![#(#args),*],
                                )
                            }}
                        }
                        Fields::Unit => quote! {{
                            let ctor_name = _gluon_base::symbol::Symbol::from(#ident);
                            _gluon_base::types::Field::ctor(
                                ctor_name, vec![],
                            )
                        }},
                    }
                    //----------------------------------------------------

                    //----------------------------------------------------
                });
                quote! {
                    _gluon_base::types::Type::variant(
                        vec![#(#variants),*]
                    )
                }
            }
            _ => panic!(
                "Only structs and enums can derive `VmType` without using the `vm_type` attribute"
            ),
        },
    };

    let associated_type_generics = generics.params.iter().map(|param| match param {
        GenericParam::Type(ty) => quote!( #ty :: Type ),
        GenericParam::Lifetime(_) => quote!( 'static ),
        GenericParam::Const(c) => quote!( #c ),
    });

    let dummy_const = Ident::new(&format!("_IMPL_VM_TYPE_FOR_{}", ident), Span::call_site());

    let make_type_impl = if container.newtype {
        let type_application = gen_type_application(&generics);
        let generic_params = map_type_params(&generics, |param| {
            let lower_param = param.to_string().to_ascii_lowercase();
            quote! {
                vm.global_env().get_generic(#lower_param)
            }
        });

        quote! {
            let ty = if let Some(ty) = vm.get_cache_alias(stringify!(#ident)) {
                ty
            } else {
                let ty = _gluon_base::types::Alias::new(
                    _gluon_base::symbol::Symbol::from(stringify!(#ident)),
                    vec![#(#generic_params),*],
                    #make_type_impl,
                );
                vm.cache_alias(ty)
            };
            #type_application
        }
    } else {
        make_type_impl
    };

    quote! {
        #[allow(non_upper_case_globals)]
        const #dummy_const: () = {
            #gluon

            #[automatically_derived]
            #[allow(unused_attributes, unused_variables)]
            impl #impl_generics _gluon_api::VmType for #ident #ty_generics
            #where_clause #(#trait_bounds,)*
            {
                type Type = #ident<
                        #(#associated_type_generics),*
                    >;

                fn make_type(vm: &_gluon_thread::Thread) -> _gluon_base::types::ArcType {
                    #make_type_impl
                }
            }
        };
    }
}

fn gen_type_application(generics: &Generics) -> TokenStream {
    let applications = map_type_params(generics, |param| {
        quote! {
            _gluon_base::types::AppVec::push(&mut vec, <#param as _gluon_api::VmType>::make_type(vm));
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
            let mut vec = _gluon_base::types::AppVec::new();
            #(#applications)*
            _gluon_base::types::Type::app(ty, vec)
        }
    }
}
