#![crate_type="lib"]
#![feature(as_unsafe_cell, box_syntax, collections, core_intrinsics, raw, slice_patterns)]
#![cfg_attr(test, feature(test))]
extern crate collections;
#[macro_use]
extern crate log;
extern crate env_logger;
#[cfg(test)]
extern crate test;

extern crate base;
extern crate parser;
extern crate check;

pub use base::interner::InternedStr;
pub use check::typecheck::TcType;
pub use compiler::{CompiledFunction, Instruction};

pub use base::{ast, gc, interner};

pub mod compiler;
#[macro_use]
pub mod vm;
mod fixed;


#[cfg(test)]
pub mod tests {
    use std::rc::Rc;
    use std::cell::RefCell;
    use base::interner::*;
    use base::gc::Gc;

///Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<(Interner, Gc)>> {
    thread_local!(static INTERNER: Rc<RefCell<(Interner, Gc)>> = Rc::new(RefCell::new((Interner::new(), Gc::new()))));
    INTERNER.with(|interner| interner.clone())
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    let mut i = i.borrow_mut();
    let &mut(ref mut i, ref mut gc) = &mut *i;
    i.intern(gc, s)
}

}
