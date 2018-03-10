//! The base crate contains pervasive types used in the compiler such as type representations, the
//! AST and some basic containers.
#![doc(html_root_url = "https://docs.rs/gluon_base/0.7.1")] // # GLUON

#[macro_use]
extern crate collect_mac;
extern crate itertools;
#[macro_use]
extern crate log;
extern crate pretty;
#[macro_use]
extern crate quick_error;
extern crate smallvec;

extern crate ordered_float;
#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "serde_derive_state")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde")]
extern crate serde_state as serde;

macro_rules! type_cache {
    ($name: ident ($($args: ident),*) { $typ: ty, $inner_type: ident } $( $id: ident )+) => {

        #[derive(Debug, Clone)]
        pub struct $name<$($args),*> {
            $(pub $id : $typ,)+
            _marker: ::std::marker::PhantomData<( $($args),* )>,
        }

        impl<$($args),*> Default for $name<$($args),*>
            where $typ: From<$inner_type<$($args,)*>> + Clone,
        {
            fn default() -> Self {
                $name::new()
            }
        }

        impl<$($args),*> $name<$($args),*>
            where $typ: From<$inner_type<$($args,)*>> + Clone,
        {
            pub fn new() -> Self {
                $name {
                    $(
                        $id : $inner_type::$id(),
                    )+
                    _marker: ::std::marker::PhantomData,
                }
            }

            $(
                pub fn $id(&self) -> $typ {
                    self.$id.clone()
                }
            )+
        }
    }
}

macro_rules! chain {
    ($alloc: expr; $first: expr, $($rest: expr),+) => {{
        let mut doc = ::pretty::DocBuilder($alloc, $first.into());
        $(
            doc = doc.append($rest);
        )*
        doc
    }}
}

#[macro_use]
pub mod macros;
pub mod ast;
pub mod error;
pub mod fixed;
pub mod fnv;
pub mod kind;
pub mod merge;
pub mod metadata;
pub mod pos;
pub mod resolve;
pub mod scoped_map;
#[cfg(feature = "serde")]
pub mod serialization;
pub mod source;
pub mod symbol;
pub mod types;

pub fn filename_to_module(filename: &str) -> String {
    use std::path::Path;
    let filename = filename.trim_right_matches('/');
    let path = Path::new(filename);
    let name = path.extension().map_or(filename, |ext| {
        ext.to_str()
            .map(|ext| &filename[..filename.len() - ext.len() - 1])
            .unwrap_or(filename)
    });

    name.replace(|c: char| c == '/' || c == '\\', ".")
}
