//! The `check` crate is responsible for ensuring that an AST expression is actually a valid
//! program. This currently consits of three larger parts, typechecking, kindchecking and renaming.
//! If an AST passes the checks in `Typecheck::typecheck_expr` (which runs all of theses checks
//! the expression is expected to compile succesfully (if it does not it should be considered an
//! internal compiler error.
#![doc(html_root_url = "https://docs.rs/gluon_check/0.9.4")] // # GLUON

extern crate codespan;
extern crate codespan_reporting;
#[macro_use]
extern crate collect_mac;
#[cfg(test)]
extern crate env_logger;
extern crate itertools;
#[macro_use]
extern crate log;
extern crate pretty;
extern crate rpds;
extern crate smallvec;
extern crate stable_deref_trait;
extern crate strsim;
extern crate union_find;

#[macro_use]
extern crate gluon_base as base;

pub mod kindcheck;
pub mod metadata;
mod recursion_check;
pub mod rename;
pub mod substitution;
pub mod typecheck;
pub mod unify;
pub mod unify_type;

mod implicits;

use base::types::{ArcType, TypeCache, TypeEnv};

/// Checks if `actual` can be assigned to a binding with the type signature `signature`
pub fn check_signature(env: &TypeEnv, signature: &ArcType, actual: &ArcType) -> bool {
    use base::{fnv::FnvMap, kind::Kind};

    use substitution::Substitution;

    let subs = Substitution::new(Kind::typ());
    let type_cache = TypeCache::new();
    let state = unify_type::State::new(env, &subs, &type_cache);
    let actual = unify_type::new_skolem_scope(&subs, actual);
    let actual = actual.instantiate_generics(&mut FnvMap::default());
    let result = unify_type::subsumes(&subs, state, signature, &actual);
    if let Err((_, ref err)) = result {
        warn!("Check signature error: {}", err);
    }
    result.is_ok()
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use base::kind::{ArcKind, KindEnv};
    use base::symbol::{Symbol, SymbolModule, SymbolRef, Symbols};
    use base::types::{Alias, ArcType, TypeEnv};

    pub struct MockEnv;

    impl KindEnv for MockEnv {
        fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
            None
        }
    }

    impl TypeEnv for MockEnv {
        fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
            None
        }
        fn find_type_info(&self, _id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
            None
        }
    }

    /// Returns a reference to the interner stored in TLD
    pub fn get_local_interner() -> Rc<RefCell<Symbols>> {
        thread_local!(static INTERNER: Rc<RefCell<Symbols>>
        = Rc::new(RefCell::new(Symbols::new())));
        INTERNER.with(|interner| interner.clone())
    }

    pub fn intern(s: &str) -> Symbol {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();

        if s.starts_with(char::is_lowercase) {
            interner.symbol(s)
        } else {
            SymbolModule::new("test".into(), &mut interner).scoped_symbol(s)
        }
    }
}
