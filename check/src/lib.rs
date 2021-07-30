//! The `check` crate is responsible for ensuring that an AST expression is actually a valid
//! program. This currently consits of three larger parts, typechecking, kindchecking and renaming.
//! If an AST passes the checks in `Typecheck::typecheck_expr` (which runs all of theses checks
//! the expression is expected to compile succesfully (if it does not it should be considered an
//! internal compiler error.
#![doc(html_root_url = "https://docs.rs/gluon_check/0.17.2")] // # GLUON

#[macro_use]
extern crate collect_mac;
#[cfg(test)]
extern crate env_logger;
#[macro_use]
extern crate log;

#[macro_use]
extern crate gluon_base as base;
#[macro_use]
extern crate gluon_codegen;

pub mod kindcheck;
pub mod metadata;
mod recursion_check;
pub mod rename;
pub mod substitution;
mod typ;
pub mod typecheck;
pub mod unify;
pub mod unify_type;

mod implicits;

use crate::base::{
    fnv::FnvMap,
    kind::Kind,
    metadata::MetadataEnv,
    symbol::Symbol,
    types::{translate_type, ArcType, PrimitiveEnv, SharedInterner, TypeEnv, TypeExt},
};

use crate::{substitution::Substitution, typ::RcType};

/// Checks if `actual` can be assigned to a binding with the type signature `signature`
pub fn check_signature(
    env: &dyn TypecheckEnv<Type = ArcType>,
    signature: &ArcType,
    actual: &ArcType,
) -> bool {
    let interner = SharedInterner::default();
    let signature = translate_type(&mut &interner, signature);
    let actual = translate_type(&mut &interner, actual);
    check_signature_(&env, &interner, &signature, &actual)
}

fn check_signature_(
    env: &dyn TypeEnv<Type = RcType>,
    interner: &SharedInterner<Symbol, RcType>,
    signature: &RcType,
    actual: &RcType,
) -> bool {
    let subs = Substitution::new(Kind::typ(), interner.clone());
    let state = unify_type::State::new(env, &subs);
    let actual = actual.instantiate_generics(&mut &subs, &mut FnvMap::default());
    let result = unify_type::subsumes(&subs, state, signature, &actual);
    if let Err((_, ref err)) = result {
        warn!("Check signature error: {}", err);
    }
    result.is_ok()
}

pub trait TypecheckEnv: PrimitiveEnv + MetadataEnv {}

impl<T> TypecheckEnv for T where T: PrimitiveEnv + MetadataEnv {}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{cell::RefCell, rc::Rc};

    use crate::base::{
        kind::{ArcKind, KindEnv},
        symbol::{Symbol, SymbolModule, SymbolRef, Symbols},
        types::{Alias, TypeEnv},
    };

    pub struct MockEnv;

    impl KindEnv for MockEnv {
        fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
            None
        }
    }

    impl TypeEnv for MockEnv {
        type Type = RcType;
        fn find_type(&self, _id: &SymbolRef) -> Option<ArcType> {
            None
        }
        fn find_type_info(&self, _id: &SymbolRef) -> Option<Alias<Symbol, RcType>> {
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
            interner.simple_symbol(s)
        } else {
            SymbolModule::new("test".into(), &mut interner).scoped_symbol(s)
        }
    }
}
