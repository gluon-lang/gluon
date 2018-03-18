//! Crate which contain the virtual machine which executes gluon programs
#![doc(html_root_url = "https://docs.rs/gluon_vm/0.5.0")]
// # GLUON
#![recursion_limit = "1024"]

#[macro_use]
extern crate bitflags;
#[macro_use]
extern crate collect_mac;
#[cfg(test)]
extern crate env_logger;
#[doc(hidden)]
pub extern crate frunk_core;
#[macro_use]
extern crate futures;
extern crate itertools;
#[macro_use]
extern crate log;
#[macro_use]
extern crate mopa;
extern crate pretty;
#[macro_use]
extern crate quick_error;
#[cfg(not(target_arch = "wasm32"))]
extern crate tokio_core;

#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive;
#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde_state")]
#[macro_use]
extern crate serde_state as serde;

#[macro_use]
extern crate gluon_base as base;
extern crate gluon_check as check;

#[macro_use]
#[cfg(feature = "serde")]
pub mod serialization;

#[macro_use]
pub mod api;
pub mod channel;
pub mod core;
pub mod compiler;
pub mod debug;
pub mod dynamic;
#[macro_use]
pub mod future;
pub mod gc;
pub mod lazy;
pub mod macros;
pub mod thread;
pub mod primitives;
pub mod reference;
pub mod stack;
pub mod types;
pub mod vm;

mod array;
mod interner;
mod source_map;
mod value;

use std::marker::PhantomData;

use api::{ValueRef, VmType};
use value::{Value, ValueRepr};
use types::VmIndex;
use base::types::ArcType;
use base::symbol::Symbol;
use base::metadata::Metadata;
use thread::{RootedThread, RootedValue, Thread};

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Variants<'a>(ValueRepr, PhantomData<&'a Value>);

impl<'a> Variants<'a> {
    /// Creates a new `Variants` value which assumes that `value` is rooted for the lifetime of the
    /// value
    pub unsafe fn new(value: &Value) -> Variants {
        Variants::with_root(value.get_repr(), value)
    }

    pub(crate) unsafe fn with_root<T: ?Sized>(value: ValueRepr, _root: &T) -> Variants {
        Variants(value, PhantomData)
    }

    pub(crate) fn get_value(&self) -> Value {
        self.0.into()
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
            display("Expected a value of type `{}` but the returned type was `{}`",
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
            from()
        }
        Interrupted {
            display("Thread was interrupted")
        }
        Panic(err: String) {
            display("{}", err)
        }
    }
}

pub type ExternLoader = fn(&Thread) -> Result<ExternModule>;

pub struct ExternModule {
    pub metadata: Metadata,
    pub value: RootedValue<RootedThread>,
    pub typ: ArcType,
}

impl ExternModule {
    pub fn new<'vm, T>(thread: &'vm Thread, value: T) -> Result<ExternModule>
    where
        T: VmType + api::Pushable<'vm> + Send + Sync,
    {
        ExternModule::with_metadata(thread, value, Metadata::default())
    }

    pub fn with_metadata<'vm, T>(
        thread: &'vm Thread,
        value: T,
        metadata: Metadata,
    ) -> Result<ExternModule>
    where
        T: VmType + api::Pushable<'vm> + Send + Sync,
    {
        Ok(ExternModule {
            value: value.marshal(thread)?,
            typ: T::make_forall_type(thread),
            metadata,
        })
    }
}

/// Internal types and functions exposed to the main `gluon` crate
pub mod internal {
    pub use value::{Value, ValuePrinter};
    pub use vm::Global;
}
