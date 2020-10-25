#![doc(html_root_url = "https://docs.rs/gluon_base/0.17.2")] // # GLUON
#![allow(unknown_lints)]
//! The base crate contains pervasive types used in the compiler such as type representations, the
//! AST and some basic containers.

#[macro_use]
extern crate collect_mac;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "serde_derive_state")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde")]
extern crate serde_state as serde;

use std::fmt;

macro_rules! type_cache {
    ($name: ident ($($args: ident),*) $( where [ $($where_: tt)* ] )? ($($arg: ident : $arg_type: ty),*) { $typ: ty, $inner_type: ident } $( $id: ident )+) => {

        #[derive(Debug, Clone)]
        pub struct $name<$($args),*>
            $(where $($where_)* )?
        {
            $(pub $arg : $arg_type,)*
            $(pub $id : $typ,)+
            _marker: ::std::marker::PhantomData<( $($args),* )>,
        }

        impl<$($args),*> Default for $name<$($args),*>
            where
                $typ: From<$inner_type<$($args,)*>>,
                $( $($where_)* )?
        {
            fn default() -> Self {
                $name::new()
            }
        }

        impl<$($args),*> $name<$($args),*>
            where
                $typ: From<$inner_type<$($args,)*>>,
                $( $($where_)* )?
        {
            pub fn new() -> Self {
                $name {
                    $($arg: <$arg_type>::default(),)*
                    $(
                        $id : $inner_type::$id(),
                    )+
                    _marker: ::std::marker::PhantomData,
                }
            }
        }

        impl<$($args),*> $name<$($args),*>
            where
                $typ: Clone,
                $( $($where_)* )?
        {
            $(
                pub fn $id(&self) -> $typ {
                    self.$id.clone()
                }
            )+
        }
    }
}

#[macro_export]
macro_rules! chain {
    ($alloc: expr, $first: expr, $($rest: expr),+ $(,)?) => {{
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
#[macro_use]
pub mod types;

pub fn filename_to_module(filename: &str) -> String {
    use std::path::Path;
    let filename = filename.trim_end_matches('/');
    let path = Path::new(filename);
    let name = path.extension().map_or(filename, |ext| {
        ext.to_str()
            .and_then(|ext| {
                if ext == "glu" {
                    Some(&filename[..filename.len() - ext.len() - 1])
                } else {
                    None
                }
            })
            .unwrap_or(filename)
    });

    name.trim_start_matches(|c: char| c == '.' || c == '/')
        .replace(|c: char| c == '/' || c == '\\', ".")
}

#[derive(Debug, Clone)]
pub enum DebugLevel {
    None,
    Low,
    High,
}

impl Default for DebugLevel {
    fn default() -> DebugLevel {
        DebugLevel::None
    }
}

impl ::std::str::FromStr for DebugLevel {
    type Err = &'static str;
    fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
        use self::DebugLevel::*;
        Ok(match s {
            "none" => None,
            "low" => Low,
            "high" => High,
            _ => return Err("Expected on of none, low, high"),
        })
    }
}

impl fmt::Display for DebugLevel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::DebugLevel::*;
        write!(
            f,
            "{}",
            match self {
                &None => "none",
                &Low => "low",
                &High => "high",
            }
        )
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn filename_to_module_test() {
        assert_eq!(filename_to_module("./main.glu"), "main");
        assert_eq!(filename_to_module("main.glu"), "main");
        assert_eq!(filename_to_module("./main/test.glu"), "main.test");
        assert_eq!(filename_to_module("main/test.glu"), "main.test");
    }
}
