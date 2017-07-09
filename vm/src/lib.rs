//! Crate which contain the virtual machine which executes gluon programs
#![doc(html_root_url="https://docs.rs/gluon_vm/0.5.0")] // # GLUON
#![recursion_limit = "1024"]

#[doc(hidden)]
pub extern crate frunk_core;
#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate mopa;
#[macro_use]
extern crate collect_mac;
#[macro_use]
extern crate bitflags;
extern crate itertools;
extern crate pretty;
#[macro_use]
extern crate futures;

#[cfg(feature = "serde")]
#[macro_use]
extern crate serde;
#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate gluon_base as base;
extern crate gluon_check as check;

#[macro_use]
pub mod serialization;

#[macro_use]
pub mod api;
pub mod channel;
pub mod compiler;
pub mod debug;
pub mod dynamic;
#[macro_use]
pub mod future;
pub mod gc;
pub mod macros;
pub mod thread;
pub mod primitives;
pub mod reference;
pub mod stack;
pub mod types;

mod array;
mod core;
mod field_map;
mod interner;
mod lazy;
mod source_map;
mod value;
mod vm;

use std::marker::PhantomData;

use api::ValueRef;
use value::Value;
use types::VmIndex;
use base::types::ArcType;
use base::symbol::Symbol;

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

#[derive(Copy, Clone, Debug)]
pub struct Variants<'a>(Value, PhantomData<&'a Value>);

impl<'a> Variants<'a> {
    /// Creates a new `Variants` value which assumes that `value` is rooted for the lifetime of the
    /// value
    pub unsafe fn new(value: &Value) -> Variants {
        Variants::with_root(*value, value)
    }

    pub unsafe fn with_root<T: ?Sized>(value: Value, _root: &T) -> Variants {
        Variants(value, PhantomData)
    }

    /// Returns an instance of `ValueRef` which allows users to safely retrieve the interals of a
    /// value
    pub fn as_ref(&self) -> ValueRef<'a> {
        unsafe { ValueRef::rooted_new(self.0) }
    }
}

/// Type returned from vm functions which may fail
pub type Result<T> = ::std::result::Result<T, Error>;

quick_error! {
    /// Representation of all possible errors that can occur when interacting with the `vm` crate
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Dead {
        }
        UndefinedBinding(symbol: String) {
            display("Binding `{}` is not defined", symbol)
        }
        UndefinedField(typ: ArcType, field: String) {
            display("Type `{}` does not have the field `{}`", typ, field)
        }
        TypeAlreadyExists(symbol: String) {
            display("Type `{}` already exists", symbol)
        }
        GlobalAlreadyExists(symbol: Symbol) {
            display("Global `{}` already exists", symbol)
        }
        MetadataDoesNotExist(symbol: String) {
            display("No metadata exists for `{}`", symbol)
        }
        WrongType(expected: ArcType, actual: ArcType) {
            display("Expected a value of type `{}` but the inferred type was `{}`",
                    expected, actual)
        }
        OutOfMemory { limit: usize, needed: usize } {
            display("Thread is out of memory: Limit {}, needed {}", limit, needed)
        }
        StackOverflow(limit: VmIndex) {
            display("The stack has overflowed: Limit `{}`", limit)
        }
        Message(err: String) {
            display("{}", err)
        }
        Panic(err: String) {
            display("{}", err)
        }
    }
}

/// Internal types and functions exposed to the main `gluon` crate
pub mod internal {
    pub use value::{Value, ClosureDataDef, ValuePrinter};
}
