//! Module providing the building blocks to create macros and expand them.
use std::error::Error as StdError;
use std::mem;
use std::sync::{Arc, Mutex, RwLock};

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, ValueBindings},
    error::Errors as BaseErrors,
    fnv::FnvMap,
    pos,
    pos::{BytePos, Spanned},
    symbol::{Symbol, Symbols},
};

use crate::thread::{RootedThread, Thread};

use futures_preview::{
    prelude::*,
    stream,
    future::BoxFuture,
    task::{Spawn, SpawnError, SpawnExt},
};

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
}

mopafy!(MacroState);
pub trait MacroState: ::mopa::Any + Send {
    fn clone_state(&self) -> Box<dyn MacroState>;
}

type SharedSpawnerInner = Arc<Mutex<dyn Spawn + Send>>;
#[derive(Clone)]
pub struct SharedSpawner {
    spawner: Option<SharedSpawnerInner>,
}

impl SharedSpawner {
    pub fn empty() -> Self {
        SharedSpawner { spawner: None }
    }

    pub fn new(spawner: Option<impl Spawn + Send + 'static>) -> Self {
        SharedSpawner {
            spawner: spawner.map(|spawner| {
                let x: SharedSpawnerInner = Arc::new(Mutex::new(spawner));
                x
            }),
        }
    }

    pub fn spawn<F>(
        &self,
        f: F,
    ) -> Result<impl Future<Output = F::Output> + Send + 'static, SpawnError>
    where
        F: Future + Send + 'static,
        F::Output: Send,
    {
        let mut f1 = None;
        let mut f2 = None;
        match &self.spawner {
            Some(spawner) => f2 = Some(spawner.lock().unwrap().spawn_with_handle(f)?),
            None => f1 = Some(f),
        }
        Ok(async move {
            match f1 {
                Some(f) => await!(f),
                None => await!(f2.unwrap()),
            }
        })
    }
}

pub struct MacroExpander {
    pub state: FnvMap<String, Box<dyn MacroState>>,
    pub task_spawner: SharedSpawner,
    pub vm: RootedThread,
    pub errors: Errors,
    pub error_in_expr: bool,
}

impl MacroExpander {
    pub fn new(vm: &Thread, task_spawner: SharedSpawner) -> MacroExpander {
        MacroExpander {
            vm: vm.root_thread(),

            state: FnvMap::default(),
            task_spawner,
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

    fn split(&self) -> Self {
        MacroExpander {
            state: self
                .state
                .iter()
                .map(|(k, v)| (k.clone(), v.clone_state()))
                .collect(),
            vm: self.vm.clone(),
            task_spawner: self.task_spawner.clone(),
            errors: Errors::new(),
            error_in_expr: self.error_in_expr.clone(),
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

            let errors = &mut self.errors;
            let task_spawner = &self.task_spawner;
            let error_in_expr = &mut self.error_in_expr;

            // Force the task spawning to happen inside the executor
            await!(future::ready(()));
            await!(
                exprs.into_iter().map(move |(expr, future)| async move {
                    // FIXME Inlining SharedSpawner::spawn is necessary to avoid ICE
                    let x = match &task_spawner.spawner {
                        Some(task_spawner) => {
                            await!(
                                match task_spawner.lock().unwrap().spawn_with_handle(future) {
                                    Ok(f) => f,
                                    Err(err) => panic!("{:#?}", err), // FIXME
                                }
                            )
                        }
                        None => await!(future),
                    };
                    (expr, x)
                })
                .collect::<stream::FuturesOrdered<_>>()
                .for_each(|(expr, (sub_expander, result))| {
                    errors.extend(sub_expander.errors);
                    *error_in_expr |= sub_expander.error_in_expr;
                    match result {
                        Ok(mut replacement) => {
                            replacement.span = expr.span;
                            replace_expr(expr, replacement);
                        }
                        Err(err) => {
                            let expr_span = expr.span;
                            replace_expr(expr, pos::spanned(expr_span, Expr::Error(None)));

                            errors.push(pos::spanned(expr.span, err));
                        }
                    }
                    future::ready(())
                })
            )
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

type MacroExprFuture =
    BoxFuture<'static, (MacroExpander, Result<SpannedExpr<Symbol>, Error>)>;
struct MacroVisitor<'b, 'c> {
    expander: &'b mut MacroExpander,
    symbols: &'c mut Symbols,
    exprs: Vec<(&'c mut SpannedExpr<Symbol>, MacroExprFuture)>,
}

impl<'b, 'c> MutVisitor<'c> for MacroVisitor<'b, 'c> {
    type Ident = Symbol;

    fn visit_expr<'d>(&'d mut self, expr: &'c mut SpannedExpr<Symbol>) {
        let replacement = match expr.value {
            Expr::App {
                ref mut implicit_args,
                func: ref mut id_expr,
                ref mut args,
            } => match id_expr.value {
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
                            let mut expander = self.expander.split();
                            Some(
                                (async move {
                                    let e = await!(m.expand(&mut expander, args));
                                    (expander, e)
                                })
                                    .boxed(),
                            )
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
