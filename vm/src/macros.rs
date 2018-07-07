//! Module providing the building blocks to create macros and expand them.
use std::any::Any;
use std::error::Error as StdError;
use std::mem;
use std::sync::{Arc, RwLock};

use futures::{stream, Future, Stream};

use base::ast::{self, Expr, MutVisitor, SpannedExpr};
use base::error::Errors as BaseErrors;
use base::fnv::FnvMap;
use base::pos;
use base::pos::{BytePos, Spanned};
use base::symbol::{Symbol, Symbols};

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
    pub fn run(
        &self,
        vm: &Thread,
        symbols: &mut Symbols,
        expr: &mut SpannedExpr<Symbol>,
    ) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm);
        expander.run(symbols, expr);
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
    pub fn new(vm: &'a Thread) -> MacroExpander<'a> {
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

    pub fn run(&mut self, symbols: &mut Symbols, expr: &mut SpannedExpr<Symbol>) {
        {
            let exprs = {
                let mut visitor = MacroVisitor {
                    expander: self,
                    symbols,
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
                            replace_expr(expr, replacement);
                            Ok(None)
                        }
                        Err(err) => {
                            let expr_span = expr.span;
                            replace_expr(expr, pos::spanned(expr_span, Expr::Error(None)));

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

fn replace_expr(expr: &mut SpannedExpr<Symbol>, new: SpannedExpr<Symbol>) {
    let expr_span = expr.span;
    let original = mem::replace(expr, pos::spanned(expr_span, Expr::Error(None)));
    *expr = pos::spanned(
        expr.span,
        Expr::MacroExpansion {
            original: Box::new(original),
            replacement: Box::new(new),
        },
    );
}

struct MacroVisitor<'a: 'b, 'b, 'c> {
    expander: &'b mut MacroExpander<'a>,
    symbols: &'c mut Symbols,
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
                        // FIXME Avoid cloning args
                        Some(m) => Some(m.expand(self.expander, args.clone())),
                        None => None,
                    }
                }
                _ => None,
            },
            Expr::TypeBindings(ref binds, ref mut body) => {
                for bind in binds {
                    if let Some(derive) = bind
                        .metadata
                        .attributes
                        .iter()
                        .find(|attr| attr.name == "derive")
                    {
                        let generated_bindings =
                            match ::derive::generate(self.symbols, derive, bind) {
                                Ok(x) => x,
                                Err(err) => {
                                    self.expander.errors.push(pos::spanned(bind.name.span, err));
                                    continue;
                                }
                            };
                        let next_expr = mem::replace(body, Default::default());
                        **body = pos::spanned(
                            Default::default(),
                            Expr::LetBindings(generated_bindings, next_expr),
                        );
                    }
                }
                None
            }
            _ => None,
        };
        if let Some(future) = replacement {
            self.exprs.push((expr, future));
        } else {
            ast::walk_mut_expr(self, expr);
        }
    }
}
