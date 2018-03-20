//! Module providing the building blocks to create macros and expand them.
use std::any::Any;
use std::mem;
use std::sync::{Arc, RwLock};
use std::error::Error as StdError;

use futures::{stream, Future, Stream};

use base::ast::{self, Expr, MutVisitor, SpannedExpr};
use base::pos::{BytePos, Spanned};
use base::error::Errors as BaseErrors;
use base::fnv::FnvMap;
use base::pos;
use base::symbol::Symbol;

use thread::Thread;

pub type Error = Box<StdError + Send + Sync>;
pub type SpannedError = Spanned<Error, BytePos>;
pub type Errors = BaseErrors<SpannedError>;
pub type MacroFuture = Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send>;

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: ::mopa::Any + Send + Sync {
    fn expand(&self, env: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture;
}

mopafy!(Macro);

impl<F: ::mopa::Any + Clone + Send + Sync> Macro for F
where
    F: Fn(&mut MacroExpander, Vec<SpannedExpr<Symbol>>)
        -> Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send>,
{
    fn expand(
        &self,
        env: &mut MacroExpander,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send> {
        self(env, args)
    }
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
#[derive(Default)]
pub struct MacroEnv {
    macros: RwLock<FnvMap<String, Arc<Macro>>>,
}

impl MacroEnv {
    /// Creates a new `MacroEnv`
    pub fn new() -> MacroEnv {
        MacroEnv {
            macros: RwLock::new(FnvMap::default()),
        }
    }

    /// Inserts a `Macro` which acts on any occurance of `symbol` when applied to an expression.
    pub fn insert<M>(&self, name: String, mac: M)
    where
        M: Macro + 'static,
    {
        self.macros.write().unwrap().insert(name, Arc::new(mac));
    }

    /// Retrieves the macro bound to `symbol`
    pub fn get(&self, name: &str) -> Option<Arc<Macro>> {
        self.macros.read().unwrap().get(name).cloned()
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub fn run(&self, vm: &Thread, expr: &mut SpannedExpr<Symbol>) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm);
        expander.run(expr);
        expander.finish()
    }
}

pub struct MacroExpander<'a> {
    pub state: FnvMap<String, Box<Any>>,
    pub vm: &'a Thread,
    pub errors: Errors,
    pub error_in_expr: bool,
    macros: &'a MacroEnv,
}

impl<'a> MacroExpander<'a> {
    pub fn new(vm: &Thread) -> MacroExpander {
        MacroExpander {
            vm: vm,
            state: FnvMap::default(),
            macros: vm.get_macros(),
            error_in_expr: false,
            errors: Errors::new(),
        }
    }

    pub fn finish(self) -> Result<(), Errors> {
        if self.error_in_expr || self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub fn run(&mut self, expr: &mut SpannedExpr<Symbol>) {
        {
            let exprs = {
                let mut visitor = MacroVisitor {
                    expander: self,
                    exprs: Vec::new(),
                };
                visitor.visit_expr(expr);
                visitor.exprs
            };
            let _ = stream::futures_ordered(exprs.into_iter().map(move |(expr, future)| {
                future.then(move |result| -> Result<_, ()> {
                    match result {
                        Ok(mut replacement) => {
                            replacement.span = expr.span;
                            *expr = replacement;
                            Ok(None)
                        }
                        Err(err) => {
                            *expr = pos::spanned(expr.span, Expr::Error(None));

                            Ok(Some(pos::spanned(expr.span, err)))
                        }
                    }
                })
            })).for_each(|err| -> Result<(), ()> {
                if let Some(err) = err {
                    self.errors.push(err);
                }
                Ok(())
            })
                .wait();
        }
        if self.errors.has_errors() {
            info!("Macro errors: {}", self.errors);
        }
    }
}

struct MacroVisitor<'a: 'b, 'b, 'c> {
    expander: &'b mut MacroExpander<'a>,
    exprs: Vec<(&'c mut SpannedExpr<Symbol>, MacroFuture)>,
}

impl<'a, 'b, 'c> MutVisitor<'c> for MacroVisitor<'a, 'b, 'c> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &'c mut SpannedExpr<Symbol>) {
        let replacement = match expr.value {
            Expr::App {
                ref mut implicit_args,
                func: ref mut id,
                ref mut args,
            } => match id.value {
                Expr::Ident(ref id) if id.name.as_ref().ends_with('!') => {
                    if !implicit_args.is_empty() {
                        self.expander.errors.push(pos::spanned(
                            expr.span,
                            "Implicit arguments are not allowed on macros".into(),
                        ));
                    }

                    let name = id.name.as_ref();
                    match self.expander.macros.get(&name[..name.len() - 1]) {
                        Some(m) => Some(m.expand(self.expander, mem::replace(args, Vec::new()))),
                        None => None,
                    }
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(future) = replacement {
            self.exprs.push((expr, future));
        } else {
            ast::walk_mut_expr(self, expr);
        }
    }
}
