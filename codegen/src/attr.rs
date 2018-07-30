use proc_macro2::{Group, Span, TokenStream, TokenTree};

use syn::synom::{ParseError, Synom};
use syn::Meta::*;
use syn::{self, Ident};

fn get_gluon_meta_items(attr: &syn::Attribute) -> Option<Vec<syn::NestedMeta>> {
    if attr.path.segments.len() == 1 && attr.path.segments[0].ident == "gluon" {
        match attr.interpret_meta() {
            Some(List(ref meta)) => Some(meta.nested.iter().cloned().collect()),
            _ => None,
        }
    } else {
        None
    }
}

pub enum CrateName {
    Some(syn::Path),
    GluonVm,
    None,
}

pub struct Container {
    pub crate_name: CrateName,
}

impl Container {
    pub fn from_ast(item: &syn::DeriveInput) -> Container {
        use syn::NestedMeta::*;

        let mut crate_name = CrateName::None;

        for meta_items in item.attrs.iter().filter_map(get_gluon_meta_items) {
            for meta_item in meta_items {
                match meta_item {
                    // Parse `#[gluon(crate_name = "foo")]`
                    Meta(NameValue(ref m)) if m.ident == "crate_name" => {
                        if let Ok(path) = parse_lit_into_path(&m.ident, &m.lit) {
                            crate_name = CrateName::Some(path);
                        }
                    }

                    // Parse `#[gluon(gluon_vm)]`
                    Meta(Word(ref w)) if w == "gluon_vm" => {
                        crate_name = CrateName::GluonVm;
                    }

                    Meta(NameValue(ref m)) if m.ident == "vm_type" => {}

                    _ => {
                        panic!("unexpected gluon container attribute");
                    }
                }
            }
        }

        Container { crate_name }
    }
}

fn get_lit_str<'a>(
    _attr_name: &Ident,
    _meta_item_name: &Ident,
    lit: &'a syn::Lit,
) -> Result<&'a syn::LitStr, ()> {
    if let syn::Lit::Str(ref lit) = *lit {
        Ok(lit)
    } else {
        panic!("Expected attribute to be a string")
    }
}

fn parse_lit_into_path(attr_name: &Ident, lit: &syn::Lit) -> Result<syn::Path, ()> {
    let string = get_lit_str(attr_name, attr_name, lit)?;
    parse_lit_str(string).map_err(|_| panic!("failed to parse path: {:?}", string.value()))
}

fn parse_lit_str<T>(s: &syn::LitStr) -> Result<T, ParseError>
where
    T: Synom,
{
    let tokens = spanned_tokens(s)?;
    syn::parse2(tokens)
}

fn spanned_tokens(s: &syn::LitStr) -> Result<TokenStream, ParseError> {
    let stream = syn::parse_str(&s.value())?;
    Ok(respan_token_stream(stream, s.span()))
}

fn respan_token_stream(stream: TokenStream, span: Span) -> TokenStream {
    stream
        .into_iter()
        .map(|token| respan_token_tree(token, span))
        .collect()
}

fn respan_token_tree(mut token: TokenTree, span: Span) -> TokenTree {
    if let TokenTree::Group(ref mut g) = token {
        *g = Group::new(g.delimiter(), respan_token_stream(g.stream().clone(), span));
    }
    token.set_span(span);
    token
}
