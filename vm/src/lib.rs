//! Crate which contain the virtual machine which executes gluon programs

#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate mopa;

extern crate gluon_base as base;

#[macro_use]
pub mod api;
pub mod compiler;
pub mod types;
pub mod vm;
pub mod thread;
pub mod interner;
pub mod gc;
pub mod stack;
pub mod primitives;
pub mod channel;
mod reference;
mod lazy;
mod array;
mod value;

use api::ValueRef;
use value::Value;

#[derive(Debug)]
pub struct Variants<'a>(&'a Value);

impl<'a> Variants<'a> {
    pub unsafe fn new(value: &Value) -> Variants {
        Variants(value)
    }

    pub fn as_ref(&self) -> ValueRef {
        ValueRef::new(self.0)
    }
}
