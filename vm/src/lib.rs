//! Crate which contain the virtual machine which executes gluon programs
#![doc(html_root_url = "https://docs.rs/gluon_vm/0.18.0")] // # GLUON
#![recursion_limit = "1024"]

#[macro_use]
extern crate collect_mac;
#[doc(hidden)]
pub extern crate frunk_core;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;
#[cfg(feature = "serde_derive")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde_state")]
#[macro_use]
extern crate serde_state as serde;
#[cfg(feature = "serde_state")]
extern crate serde_json;

#[cfg(test)]
extern crate env_logger;

#[macro_use]
pub extern crate gluon_base as base;
extern crate gluon_check as check;
#[macro_use]
extern crate gluon_codegen;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

pub type BoxFuture<'vm, T, E> = futures::future::BoxFuture<'vm, std::result::Result<T, E>>;

macro_rules! alloc {
    ($context: ident, $data: expr) => {
        $crate::thread::alloc($context.gc, $context.thread, &$context.stack.stack(), $data)
    };
}

#[macro_use]
#[cfg(feature = "serde")]
pub mod serialization;

#[macro_use]
pub mod gc;

#[macro_use]
pub mod api;
pub mod channel;
pub mod compiler;
pub mod core;
pub mod debug;
pub mod dynamic;
pub mod lazy;
pub mod macros;
pub mod primitives;
pub mod reference;
pub mod stack;
pub mod thread;
pub mod types;
pub mod vm;

mod array;
mod derive;
mod interner;
mod source_map;
mod value;

use std::{self as real_std, fmt, marker::PhantomData};

use crate::base::{metadata::Metadata, source::FileId, symbol::Symbol, types::ArcType};
use crate::{
    api::{ValueRef, VmType},
    gc::CloneUnrooted,
    stack::Stacktrace,
    thread::{RootedThread, RootedValue, Thread},
    types::{VmIndex, VmInt},
    value::{Value, ValueRepr},
};

use codespan_reporting::diagnostic::Diagnostic;

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

#[derive(Debug, PartialEq, Trace)]
#[gluon(gluon_vm)]
#[repr(transparent)]
pub struct Variants<'a>(ValueRepr, PhantomData<&'a Value>);

impl Clone for Variants<'_> {
    fn clone(&self) -> Self {
        // SAFETY Cloning keeps the same lifetime as `self`
        unsafe { Variants(self.0.clone_unrooted(), self.1) }
    }
}

impl<'a> Variants<'a> {
    /// Creates a new `Variants` value which assumes that `value` is rooted for the lifetime of the
    /// value
    #[inline]
    pub fn new(value: &Value) -> Variants {
        // SAFETY The returned value is tied to the lifetime of the `value` root meaning the
        // variant is also rooted
        unsafe { Variants::with_root(value, value) }
    }

    #[inline]
    pub(crate) unsafe fn with_root<'r, T: ?Sized>(value: &Value, _root: &'r T) -> Variants<'r> {
        Variants(value.get_repr().clone_unrooted(), PhantomData)
    }

    #[inline]
    pub(crate) fn int(i: VmInt) -> Self {
        Variants(ValueRepr::Int(i), PhantomData)
    }

    #[inline]
    pub(crate) fn tag(i: VmIndex) -> Self {
        Variants(ValueRepr::Tag(i), PhantomData)
    }

    #[inline]
    pub fn get_value(&self) -> &Value {
        Value::from_ref(&self.0)
    }

    #[inline]
    pub(crate) fn get_repr(&self) -> &ValueRepr {
        &self.0
    }

    pub(crate) unsafe fn unrooted(&self) -> Value {
        Value::from(self.0.clone_unrooted())
    }

    /// Returns an instance of `ValueRef` which allows users to safely retrieve the interals of a
    /// value
    #[inline]
    pub fn as_ref(&self) -> ValueRef<'a> {
        unsafe { ValueRef::rooted_new(&self.0) }
    }
}

/// Type returned from vm functions which may fail
pub type Result<T> = ::std::result::Result<T, Error>;

quick_error! {
    /// Representation of all possible errors that can occur when interacting with the `vm` crate
    #[derive(Debug, Eq, PartialEq, Hash, Clone)]
    pub enum Error {
        Dead {
            display("The gluon thread is dead")
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
        Panic(err: String, stacktrace: Option<Stacktrace>) {
            display("{}", Panic { err, stacktrace })
        }
    }
}

impl base::error::AsDiagnostic for Error {
    fn as_diagnostic(&self, _map: &base::source::CodeMap) -> Diagnostic<FileId> {
        Diagnostic::error().with_message(self.to_string())
    }
}

struct Panic<'a> {
    err: &'a String,
    stacktrace: &'a Option<Stacktrace>,
}

impl<'a> fmt::Display for Panic<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Panic { err, stacktrace } = *self;
        write!(f, "{}", err)?;
        if let Some(ref stacktrace) = *stacktrace {
            write!(f, "\n\n{}", stacktrace)?;
        }
        Ok(())
    }
}

impl fmt::Debug for ExternLoader {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ExternLoader")
            .field("dependencies", &self.dependencies)
            .finish()
    }
}

pub struct ExternLoader {
    pub load_fn: Box<dyn Fn(&Thread) -> Result<ExternModule> + Send + Sync>,
    pub dependencies: Vec<String>,
}

#[derive(Debug)]
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
    pub use crate::interner::InternedStr;
    pub use crate::value::{Cloner, ClosureData, Value, ValuePrinter};
    pub use crate::vm::Global;
}
