#![feature(box_syntax)]
#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;

extern crate base;

extern crate parser;

pub use base::interner::InternedStr;

pub use base::{ast, gc, interner};

pub mod typecheck;
mod kindcheck;
mod substitution;
mod scoped_map;

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
