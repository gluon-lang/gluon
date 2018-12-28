//! Module providing the building blocks to create macros and expand them.
use std::any::Any;
use std::error::Error as StdError;
use std::mem;
use std::sync::{Arc, RwLock};

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, ValueBindings},
    error::Errors as BaseErrors,
    fnv::FnvMap,
    pos,
    pos::{BytePos, Spanned},
    symbol::{Symbol, Symbols},
};

use crate::thread::{RootedThread, Thread};

use futures_preview::{future::BoxFuture, prelude::*};

pub type Error = Box<dyn StdError + Send + Sync>;
pub type SpannedError = Spanned<Error, BytePos>;
pub type Errors = BaseErrors<SpannedError>;
pub type MacroFuture<'f> = BoxFuture<'f, Result<SpannedExpr<Symbol>, Error>>;

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: ::mopa::Any + Send + Sync {
    fn expand<'f>(
        &'f self,
        env: &'f mut MacroExpander,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> MacroFuture<'f>;
}

mopafy!(Macro);

impl<F: ::mopa::Any + Clone + Send + Sync> Macro for F
where
    F: Fn(&mut MacroExpander, Vec<SpannedExpr<Symbol>>) -> MacroFuture<'static>,
{
    fn expand<'f>(
        &'f self,
        env: &'f mut MacroExpander,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> MacroFuture<'f> {
        self(env, args)
    }
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
#[derive(Default)]
pub struct MacroEnv {
    macros: RwLock<FnvMap<String, Arc<dyn Macro>>>,
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
    pub fn get(&self, name: &str) -> Option<Arc<dyn Macro>> {
        self.macros.read().unwrap().get(name).cloned()
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub async fn run<'f>(
        &'f self,
        vm: &'f Thread,
        symbols: &'f mut Symbols,
        expr: &'f mut SpannedExpr<Symbol>,
    ) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm);
        await!(expander.run(symbols, expr));
        expander.finish()
    }
}

pub struct MacroExpander {
    pub state: FnvMap<String, Box<dyn Any + Send>>,
    pub vm: RootedThread,
    pub errors: Errors,
    pub error_in_expr: bool,
}

impl MacroExpander {
    pub fn new(vm: &Thread) -> MacroExpander {
        MacroExpander {
            vm: vm.root_thread(),

            state: FnvMap::default(),
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

    pub async fn run<'f>(
        &'f mut self,
        symbols: &'f mut Symbols,
        expr: &'f mut SpannedExpr<Symbol>,
    ) {
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

            for (expr, future) in exprs {
                match await!(future) {
                    Ok(mut replacement) => {
                        replacement.span = expr.span;
                        replace_expr(expr, replacement);
                    }
                    Err(err) => {
                        let expr_span = expr.span;
                        replace_expr(expr, pos::spanned(expr_span, Expr::Error(None)));

                        self.errors.push(pos::spanned(expr.span, err));
                    }
                }
            }
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

struct MacroVisitor<'b, 'c> {
    expander: &'b mut MacroExpander,
    symbols: &'c mut Symbols,
    exprs: Vec<(&'c mut SpannedExpr<Symbol>, MacroFuture<'c>)>,
}

impl<'b, 'c> MutVisitor<'c> for MacroVisitor<'b, 'c> {
    type Ident = Symbol;

    fn visit_expr<'d>(&'d mut self, expr: &'c mut SpannedExpr<Symbol>) {
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
                    match self.expander.vm.get_macros().get(&name[..name.len() - 1]) {
                        // FIXME Avoid cloning args
                        Some(m) => {
                            let args = args.clone();
                            // FIXME Forward macro expander, don't create a new
                            let mut expander = MacroExpander::new(&self.expander.vm);
                            Some((async move { await!(m.expand(&mut expander, args)) }).boxed())
                        }
                        None => None,
                    }
                }
                _ => None,
            },
            Expr::TypeBindings(ref binds, ref mut body) => {
                let generated_bindings = binds
                    .iter()
                    .flat_map(|bind| {
                        if let Some(derive) = bind
                            .metadata
                            .attributes
                            .iter()
                            .find(|attr| attr.name == "derive")
                        {
                            match crate::derive::generate(self.symbols, derive, bind) {
                                Ok(x) => x,
                                Err(err) => {
                                    self.expander.errors.push(pos::spanned(bind.name.span, err));
                                    Vec::new()
                                }
                            }
                        } else {
                            Vec::new()
                        }
                    })
                    .collect::<Vec<_>>();
                if !generated_bindings.is_empty() {
                    let next_expr = mem::replace(body, Default::default());
                    body.value =
                        Expr::LetBindings(ValueBindings::Recursive(generated_bindings), next_expr);
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
