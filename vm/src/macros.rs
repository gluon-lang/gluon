//! Module providing the building blocks to create macros and expand them.
use std::{
    any::{Any, TypeId},
    error::Error as StdError,
    fmt, mem,
    pin::Pin,
    sync::{Arc, RwLock},
};

use {
    codespan_reporting::diagnostic::Diagnostic,
    downcast_rs::{impl_downcast, Downcast},
    futures::{prelude::*, task::Spawn},
};

use gluon_codegen::Trace;

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr},
    error::{AsDiagnostic, Errors as BaseErrors, Salvage, SalvageResult},
    fnv::FnvMap,
    pos,
    pos::{BytePos, Spanned},
    source::FileId,
    symbol::{Symbol, Symbols},
};

use crate::{
    gc::Trace,
    thread::{RootedThread, Thread},
};

pub type SpannedError = Spanned<Error, BytePos>;
pub type Errors = BaseErrors<SpannedError>;

pub type MacroResult<'ast> = Result<SpannedExpr<'ast, Symbol>, Error>;
pub type SalvageMacroResult<'ast> = SalvageResult<SpannedExpr<'ast, Symbol>, Error>;

pub enum LazyMacroResult<'ast> {
    Done(SpannedExpr<'ast, Symbol>),
    Lazy(
        Box<
            dyn for<'a> FnOnce() -> Pin<
                    Box<dyn Future<Output = SalvageMacroResult<'ast>> + Send + 'ast>,
                > + Send
                + 'ast,
        >,
    ),
}

impl<'ast> LazyMacroResult<'ast> {
    async fn compute(self) -> SalvageMacroResult<'ast> {
        match self {
            Self::Done(r) => Ok(r),
            Self::Lazy(f) => f().await,
        }
    }
}

impl<'ast> From<SpannedExpr<'ast, Symbol>> for LazyMacroResult<'ast> {
    fn from(r: SpannedExpr<'ast, Symbol>) -> Self {
        Self::Done(r)
    }
}

impl<'ast, F> From<F> for LazyMacroResult<'ast>
where
    for<'a> F: FnOnce() -> Pin<Box<dyn Future<Output = SalvageMacroResult<'ast>> + Send + 'ast>>
        + Send
        + 'ast,
{
    fn from(r: F) -> Self {
        Self::Lazy(Box::new(r))
    }
}

pub type MacroFuture<'r, 'ast> =
    Pin<Box<dyn Future<Output = Result<LazyMacroResult<'ast>, Error>> + Send + 'r>>;

pub trait Captures<'a> {}
impl<T> Captures<'_> for T {}

pub trait DowncastArc: Downcast {
    fn into_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync>;
}

impl<T> DowncastArc for T
where
    T: Downcast + Send + Sync,
{
    fn into_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync> {
        self
    }
}

pub trait MacroError: DowncastArc + StdError + AsDiagnostic + Send + Sync + 'static {
    fn clone_error(&self) -> Error;
    fn eq_error(&self, other: &dyn MacroError) -> bool;
    fn hash_error(&self, hash: &mut dyn std::hash::Hasher);
}

impl_downcast!(MacroError);

impl dyn MacroError {
    #[inline]
    pub fn downcast_arc<T: MacroError>(self: Arc<Self>) -> Result<Arc<T>, Arc<Self>>
    where
        Self: Send + Sync,
    {
        if self.is::<T>() {
            Ok(DowncastArc::into_arc_any(self).downcast::<T>().unwrap())
        } else {
            Err(self)
        }
    }
}

impl<T> MacroError for T
where
    T: Clone + PartialEq + std::hash::Hash + AsDiagnostic + StdError + Send + Sync + 'static,
{
    fn clone_error(&self) -> Error {
        Error(Box::new(self.clone()))
    }
    fn eq_error(&self, other: &dyn MacroError) -> bool {
        other
            .downcast_ref::<Self>()
            .map_or(false, |other| self == other)
    }
    fn hash_error(&self, mut hash: &mut dyn std::hash::Hasher) {
        self.hash(&mut hash)
    }
}

#[derive(Debug)]
pub struct Error(Box<dyn MacroError>);

impl StdError for Error {
    #[allow(deprecated)]
    fn description(&self) -> &str {
        self.0.description()
    }
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.source()
    }
}

impl AsDiagnostic for Error {
    fn as_diagnostic(&self, map: &base::source::CodeMap) -> Diagnostic<FileId> {
        self.0.as_diagnostic(map)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Clone for Error {
    fn clone(&self) -> Self {
        self.0.clone_error()
    }
}

impl Eq for Error {}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq_error(&*other.0)
    }
}

impl std::hash::Hash for Error {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.0.hash_error(state)
    }
}

impl Error {
    pub fn new<E>(err: E) -> Self
    where
        E: MacroError,
    {
        Self(Box::new(err))
    }

    pub fn message(s: impl Into<String>) -> Error {
        #[derive(Debug, Eq, PartialEq, Clone, Hash)]
        struct StringError(String);

        impl StdError for StringError {
            fn description(&self) -> &str {
                &self.0
            }
        }

        impl fmt::Display for StringError {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                fmt::Display::fmt(&self.0, f)
            }
        }

        impl AsDiagnostic for StringError {
            fn as_diagnostic(&self, _map: &base::source::CodeMap) -> Diagnostic<FileId> {
                Diagnostic::error().with_message(self.to_string())
            }
        }

        Self::new(StringError(s.into()))
    }

    pub fn downcast<T>(self) -> Result<Box<T>, Self>
    where
        T: MacroError,
    {
        self.0.downcast().map_err(Self)
    }
}

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: Trace + DowncastArc + Send + Sync {
    fn get_capability<T>(&self, thread: &Thread, arc_self: &Arc<dyn Macro>) -> Option<T>
    where
        Self: Sized,
        T: Any,
    {
        self.get_capability_impl(thread, arc_self, TypeId::of::<T>())
            .map(|b| {
                *b.downcast::<T>()
                    .ok()
                    .expect("get_capability_impl return an unexpected type")
            })
    }

    fn get_capability_impl(
        &self,
        thread: &Thread,
        arc_self: &Arc<dyn Macro>,
        id: TypeId,
    ) -> Option<Box<dyn Any>> {
        let _ = (thread, arc_self, id);
        None
    }

    /// Creating a symbol in `symbols` will put it in the same scope as the code surrounding the
    /// expansion. If you want to create a unique symbol then call `Symbol::from` or create a new
    /// `Symbols` table
    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        env: &'b mut MacroExpander<'a>,
        symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast>;
}

impl_downcast!(Macro);

impl dyn Macro {
    #[inline]
    pub fn downcast_arc<T: Macro>(self: Arc<Self>) -> Result<Arc<T>, Arc<Self>>
    where
        Self: Send + Sync,
    {
        if self.is::<T>() {
            Ok(DowncastArc::into_arc_any(self).downcast::<T>().unwrap())
        } else {
            Err(self)
        }
    }
}

#[async_trait::async_trait]
impl<M> Macro for Box<M>
where
    M: Macro + ?Sized,
{
    fn get_capability_impl(
        &self,
        thread: &Thread,
        arc_self: &Arc<dyn Macro>,
        id: TypeId,
    ) -> Option<Box<dyn Any>> {
        (**self).get_capability_impl(thread, arc_self, id)
    }

    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        env: &'b mut MacroExpander<'a>,
        symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
        (**self).expand(env, symbols, arena, args)
    }
}

#[async_trait::async_trait]
impl<M> Macro for Arc<M>
where
    M: Macro + ?Sized,
{
    fn get_capability_impl(
        &self,
        thread: &Thread,
        arc_self: &Arc<dyn Macro>,
        id: TypeId,
    ) -> Option<Box<dyn Any>> {
        (**self).get_capability_impl(thread, arc_self, id)
    }

    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        env: &'b mut MacroExpander<'a>,
        symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
        (**self).expand(env, symbols, arena, args)
    }
}

pub trait MacroUserdata: Send {
    fn fork(&self, thread: RootedThread) -> Box<dyn Any>;
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
#[derive(Trace, Default)]
#[gluon(gluon_vm)]
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

    pub fn get_capabilities<T>(&self, thread: &Thread) -> Vec<T>
    where
        T: Any,
    {
        let macros = self.macros.read().unwrap();
        macros
            .values()
            .filter_map(|mac| mac.get_capability::<T>(thread, mac))
            .collect()
    }

    pub fn get_capability<T>(&self, thread: &Thread) -> Option<T>
    where
        T: Any,
    {
        let macros = self.macros.read().unwrap();
        macros
            .values()
            .find_map(|mac| mac.get_capability::<T>(thread, mac))
    }

    pub fn clear(&self) {
        self.macros.write().unwrap().clear();
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub async fn run<'ast>(
        &self,
        vm: &Thread,
        userdata: &mut (dyn MacroUserdata + '_),
        spawn: Option<&(dyn Spawn + Send + Sync + '_)>,
        symbols: &mut Symbols,
        arena: ast::OwnedArena<'ast, Symbol>,
        expr: &'ast mut SpannedExpr<'ast, Symbol>,
    ) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm, userdata, spawn);
        expander.run(symbols, arena, expr).await;
        expander.finish()
    }
}

pub struct MacroExpander<'a> {
    pub state: FnvMap<String, Box<dyn Any + Send>>,
    pub vm: &'a Thread,
    pub errors: Errors,
    pub userdata: &'a mut (dyn MacroUserdata + 'a),
    pub spawn: Option<&'a (dyn Spawn + Send + Sync + 'a)>,
    macros: &'a MacroEnv,
}

impl<'a> MacroExpander<'a> {
    pub fn new(
        vm: &'a Thread,
        userdata: &'a mut (dyn MacroUserdata + 'a),
        spawn: Option<&'a (dyn Spawn + Send + Sync + 'a)>,
    ) -> Self {
        MacroExpander {
            vm,
            state: FnvMap::default(),
            macros: vm.get_macros(),
            userdata,
            spawn,
            errors: Errors::new(),
        }
    }

    pub fn fork(&self, userdata: &'a mut (dyn MacroUserdata + 'a)) -> MacroExpander<'a> {
        MacroExpander {
            vm: self.vm,
            state: FnvMap::default(),
            macros: self.macros,
            userdata,
            spawn: self.spawn,
            errors: Errors::new(),
        }
    }

    pub fn finish(self) -> Result<(), Errors> {
        if self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub async fn run<'ast>(
        &mut self,
        symbols: &mut Symbols,
        mut arena: ast::OwnedArena<'ast, Symbol>,
        expr: &'ast mut SpannedExpr<'ast, Symbol>,
    ) {
        self.run_once(symbols, &mut arena, expr).await; // FIXME
    }

    pub async fn run_once<'ast>(
        &mut self,
        symbols: &mut Symbols,
        arena: &mut ast::OwnedArena<'ast, Symbol>,
        expr: &mut SpannedExpr<'ast, Symbol>,
    ) {
        let mut visitor = MacroVisitor {
            expander: self,
            symbols,
            arena,
            exprs: Vec::new(),
        };
        visitor.visit_expr(expr);
        let MacroVisitor { exprs, symbols, .. } = visitor;
        self.expand(symbols, arena, exprs).await
    }

    async fn expand<'ast>(
        &mut self,
        symbols: &mut Symbols,
        arena: &mut ast::OwnedArena<'ast, Symbol>,
        mut exprs: Vec<(&'_ mut SpannedExpr<'ast, Symbol>, Arc<dyn Macro>)>,
    ) {
        let mut futures = Vec::with_capacity(exprs.len());
        for (expr, mac) in exprs.drain(..) {
            let result = match &mut expr.value {
                Expr::App { args, .. } => mac.expand(self, symbols, arena, args).await,
                _ => unreachable!("{:?}", expr),
            };
            match result {
                Ok(result) => futures.push(result.compute().map(move |result| (expr, result))),
                Err(err) => {
                    self.errors.push(pos::spanned(expr.span, err));
                    replace_expr(arena, expr, Expr::Error(None));
                }
            }
        }

        // Index each expansion future so we can keep any returned errors in a consistent order
        let mut stream = futures
            .into_iter()
            .enumerate()
            .map(|(index, future)| future.map(move |x| (index, x)))
            .collect::<futures::stream::FuturesUnordered<_>>();
        let mut unordered_errors = Vec::new();
        while let Some((index, (expr, result))) = stream.next().await {
            let expr = { expr };
            let new_expr = match result {
                Ok(replacement) => replacement.value,
                Err(Salvage { error, value }) => {
                    unordered_errors.push((index, pos::spanned(expr.span, error)));
                    value.map_or_else(|| Expr::Error(None), |e| e.value)
                }
            };

            replace_expr(arena, expr, new_expr);
        }

        unordered_errors.sort_by_key(|&(index, _)| index);
        self.errors
            .extend(unordered_errors.into_iter().map(|(_, err)| err));
    }
}

fn replace_expr<'ast>(
    arena: &ast::OwnedArena<'ast, Symbol>,
    expr: &mut SpannedExpr<'ast, Symbol>,
    new: Expr<'ast, Symbol>,
) {
    let expr_span = expr.span;
    let original = mem::replace(expr, pos::spanned(expr_span, Expr::Error(None)));
    *expr = pos::spanned(
        expr.span,
        Expr::MacroExpansion {
            original: arena.alloc(original),
            replacement: arena.alloc(pos::spanned(expr_span, new)),
        },
    );
}

struct MacroVisitor<'a: 'b, 'b, 'c, 'd, 'e, 'ast> {
    expander: &'b mut MacroExpander<'a>,
    symbols: &'c mut Symbols,
    arena: &'d mut ast::OwnedArena<'ast, Symbol>,
    exprs: Vec<(&'e mut SpannedExpr<'ast, Symbol>, Arc<dyn Macro>)>,
}

impl<'a, 'b, 'c, 'e, 'ast> MutVisitor<'e, 'ast> for MacroVisitor<'a, 'b, 'c, '_, 'e, 'ast> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &'e mut SpannedExpr<'ast, Symbol>) {
        let replacement = match &mut expr.value {
            Expr::App {
                implicit_args,
                func,
                args: _,
            } => match &func.value {
                Expr::Ident(ref id) if id.name.as_str().ends_with('!') => {
                    if !implicit_args.is_empty() {
                        self.expander.errors.push(pos::spanned(
                            expr.span,
                            Error::message("Implicit arguments are not allowed on macros"),
                        ));
                    }

                    let name = id.name.as_str();
                    match self.expander.macros.get(&name[..name.len() - 1]) {
                        // FIXME Avoid cloning args
                        Some(m) => Some(m.clone()),
                        None => None,
                    }
                }
                _ => None,
            },
            Expr::TypeBindings(binds, body) => {
                let Self {
                    arena,
                    symbols,
                    expander,
                    ..
                } = self;
                let mut generated_bindings = Vec::new();
                for bind in &**binds {
                    generated_bindings.extend(
                        bind.metadata
                            .attributes()
                            .filter(|attr| attr.name == "derive")
                            .map(|derive| {
                                match crate::derive::generate(arena.borrow(), symbols, derive, bind)
                                {
                                    Ok(x) => x,
                                    Err(err) => {
                                        expander.errors.push(pos::spanned(bind.name.span, err));
                                        Vec::new()
                                    }
                                }
                            })
                            .flatten(),
                    );
                }
                if !generated_bindings.is_empty() {
                    let next_expr = mem::take(*body);
                    body.value =
                        Expr::rec_let_bindings(self.arena.borrow(), generated_bindings, next_expr);
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
