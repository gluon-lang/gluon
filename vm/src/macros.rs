//! Module providing the building blocks to create macros and expand them.
use std::any::Any;
use std::sync::{Arc, RwLock};
use std::error::Error as StdError;

use base::ast::{self, Expr, MutVisitor, SpannedExpr};
use base::error::Errors;
use base::fnv::FnvMap;
use base::symbol::Symbol;

use thread::Thread;

pub type Error = Box<StdError + Send + Sync>;

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: ::mopa::Any + Send + Sync {
    fn expand(&self,
              env: &mut MacroExpander,
              args: &mut [SpannedExpr<Symbol>])
              -> Result<SpannedExpr<Symbol>, Error>;
}

mopafy!(Macro);

impl<F: ::mopa::Any + Clone + Send + Sync> Macro for F
    where F: Fn(&mut MacroExpander, &mut [SpannedExpr<Symbol>]) -> Result<SpannedExpr<Symbol>, Error>,
{
    fn expand(&self,
              env: &mut MacroExpander,
              args: &mut [SpannedExpr<Symbol>])
              -> Result<SpannedExpr<Symbol>, Error> {
        self(env, args)
    }
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
pub struct MacroEnv {
    macros: RwLock<FnvMap<String, Arc<Macro>>>,
}

impl MacroEnv {
    /// Creates a new `MacroEnv`
    pub fn new() -> MacroEnv {
        MacroEnv { macros: RwLock::new(FnvMap::default()) }
    }

    /// Inserts a `Macro` which acts on any occurance of `symbol` when applied to an expression.
    pub fn insert<M>(&self, name: String, mac: M)
        where M: Macro + 'static,
    {
        self.macros.write().unwrap().insert(name, Arc::new(mac));
    }

    /// Retrieves the macro bound to `symbol`
    pub fn get(&self, name: &str) -> Option<Arc<Macro>> {
        self.macros.read().unwrap().get(name).cloned()
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub fn run(&self, vm: &Thread, expr: &mut SpannedExpr<Symbol>) -> Result<(), Errors<Error>> {
        let mut expander = MacroExpander::new(vm);
        expander.visit_expr(expr);
        expander.finish()
    }
}

pub struct MacroExpander<'a> {
    pub state: FnvMap<String, Box<Any>>,
    pub vm: &'a Thread,
    pub errors: Errors<Error>,
    macros: &'a MacroEnv,
}

impl<'a> MacroExpander<'a> {
    pub fn new(vm: &Thread) -> MacroExpander {
        MacroExpander {
            vm: vm,
            state: FnvMap::default(),
            macros: vm.get_macros(),
            errors: Errors::new(),
        }
    }

    pub fn finish(self) -> Result<(), Errors<Error>> {
        if self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub fn run(&mut self, expr: &mut SpannedExpr<Symbol>) {
        self.visit_expr(expr);
    }
}


impl<'a> MutVisitor for MacroExpander<'a> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
        let replacement = match expr.value {
            Expr::App(ref mut id, ref mut args) => {
                match id.value {
                    Expr::Ident(ref id) => {
                        match self.macros.get(id.name.as_ref()) {
                            Some(m) => {
                                match m.expand(self, args) {
                                    Ok(e) => Some(e),
                                    Err(err) => {
                                        self.errors.error(err);
                                        None
                                    }
                                }
                            }
                            None => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(mut e) = replacement {
            e.span = expr.span;
            *expr = e;
        }
        ast::walk_mut_expr(self, expr);
    }
}
