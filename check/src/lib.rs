//! The `check` crate does all checking on a successfully parsed AST to determine if it is a valid
//! program. If an AST passes the checks in `Typecheck::typecheck_expr` the `AST` is expected to
//! sucessfully compile as well.

#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
extern crate union_find;

extern crate base;
#[cfg(test)]
extern crate parser;

mod instantiate;
pub mod typecheck;
pub mod unify_type;
pub mod unify;
pub mod kindcheck;
mod substitution;
mod rename;

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use base::symbol::{Symbols, SymbolModule, Symbol};

    ///Returns a reference to the interner stored in TLD
    pub fn get_local_interner() -> Rc<RefCell<Symbols>> {
        thread_local!(static INTERNER: Rc<RefCell<Symbols>>
                      = Rc::new(RefCell::new(Symbols::new())));
        INTERNER.with(|interner| interner.clone())
    }

    pub fn intern(s: &str) -> Symbol {
        let i = get_local_interner();
        let mut i = i.borrow_mut();
        if s.chars().next().map(|c| c.is_lowercase()).unwrap_or(false) {
            i.symbol(s)
        } else {
            SymbolModule::new("test".into(), &mut i).scoped_symbol(s)
        }
    }
}
