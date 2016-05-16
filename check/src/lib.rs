//! The `check` crate is responsible for ensuring that an AST expression is actually a valid
//! program. This currently consits of three larger parts, typechecking, kindchecking and renaming.
//! If an AST passes the checks in `Typecheck::typecheck_expr` (which runs all of theses checks
//! the expression is expected to compile succesfully (if it does not it should be considered an
//! internal compiler error.

#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
extern crate union_find;

extern crate base;

pub mod typecheck;
pub mod unify_type;
pub mod unify;
pub mod kindcheck;
mod substitution;
mod rename;
pub mod completion;
pub mod metadata;

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
