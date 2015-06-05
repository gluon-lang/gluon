#![crate_type="lib"]
#![feature(box_syntax, core, collections, slice_patterns)]
#![cfg_attr(test, feature(test))]
extern crate collections;
#[macro_use]
extern crate log;
extern crate env_logger;
#[cfg(test)]
extern crate test;

extern crate base;
extern crate parser as parser_new;

pub use base::interner::InternedStr;
pub use typecheck::TcType;
pub use compiler::{CompiledFunction, Instruction};

pub use base::{ast, gc, interner};

mod scoped_map;
mod kindcheck;
pub mod typecheck;
pub mod compiler;
pub mod vm;
mod fixed;
#[macro_use]
pub mod api;


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
