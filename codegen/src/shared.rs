use proc_macro2::{Ident, Span, TokenStream};
use syn::{GenericParam, Generics, Lifetime, LifetimeDef, TypeGenerics, TypeParam};

/// Maps all type parameters in `generics`. The function gets passed the ident of
/// the respective type parameter.
pub fn map_type_params<F, R>(generics: &Generics, mapper: F) -> Vec<R>
where
    F: FnMut(&Ident) -> R,
{
    generics
        .params
        .iter()
        .filter_map(|param| match param {
            GenericParam::Type(param) => Some(&param.ident),
            _ => None,
        })
        .map(mapper)
        .collect()
}

/// Maps all lifetimes in `generics`.
pub fn map_lifetimes<F, R>(generics: &Generics, mapper: F) -> Vec<R>
where
    F: FnMut(&Lifetime) -> R,
{
    generics
        .params
        .iter()
        .filter_map(|param| match param {
            GenericParam::Lifetime(def) => Some(&def.lifetime),
            _ => None,
        })
        .map(mapper)
        .collect()
}

/// Processes `generics` for use in a trait implementation. Returns a tuple of type params
/// after the `impl` keyword, params after the type identifier and a where clause with all
/// necessary bounds.
///
/// The where bound always contains a `where`, even if it empty and always
/// includes a trailing comma after the last bound (if any).
/// `extra_lifetimes` allows to define lifetimes that are only part of the generic parameter
/// definition and can thus be freely used for the trait that is implemented.
pub fn split_for_impl<'a>(
    generics: &'a Generics,
    extra_params: &[&str],
    extra_lifetimes: &[&str],
) -> (TokenStream, TypeGenerics<'a>, TokenStream) {
    // add trailing comma or add a where if there are no predicates
    let (_, ty_generics, where_clause) = generics.split_for_impl();
    let ty_generics = ty_generics.clone();
    let where_clause = where_clause
        .map(|clause| {
            if clause.predicates.empty_or_trailing() {
                quote! { #clause }
            } else {
                quote! { #clause, }
            }
        })
        .unwrap_or(quote! { where });

    // generate the generic params for the impl block
    // these need the additional lifetimes
    let mut generics = generics.clone();

    extra_params
        .into_iter()
        .map(|param| GenericParam::from(TypeParam::from(Ident::new(param, Span::call_site()))))
        .for_each(|param| {
            if generics.params.iter().all(|p| *p != param) {
                generics.params.insert(0, param)
            }
        });

    extra_lifetimes
        .into_iter()
        .map(|lifetime| {
            GenericParam::from(LifetimeDef::new(Lifetime::new(lifetime, Span::call_site())))
        })
        .for_each(|lifetime| {
            if generics.params.iter().all(|p| *p != lifetime) {
                generics.params.insert(0, lifetime)
            }
        });

    let (impl_generics, ..) = generics.split_for_impl();
    (quote! { #impl_generics }, ty_generics, where_clause)
}
