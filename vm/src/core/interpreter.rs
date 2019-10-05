use std::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr, slice,
    sync::Arc,
};

use itertools::Itertools;

use crate::base::{
    ast::TypedIdent,
    fnv::FnvMap,
    kind::{ArcKind, KindEnv},
    merge::{merge, merge_collect},
    scoped_map::ScopedMap,
    symbol::{Symbol, SymbolRef},
    types::{Alias, ArcType, TypeEnv, TypeExt},
};

use crate::{
    core::{
        self,
        costs::{Cost, Costs},
        optimize::{self, walk_expr_alloc, DifferentLifetime, ExprProducer, SameLifetime, Visitor},
        purity::PurityMap,
        Allocator, Alternative, ArenaExt, CExpr, Closure, ClosureRef, CoreClosure, CoreExpr, Expr,
        LetBinding, Literal, Named, Pattern,
    },
    Error, Result,
};

#[derive(Copy, Clone, Debug)]
enum Reduced<L, G> {
    Local(L),
    Global(G),
}

impl<L, G> fmt::Display for Reduced<L, G>
where
    L: fmt::Display,
    G: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Reduced::Local(e) => e.fmt(f),
            Reduced::Global(e) => e.fmt(f),
        }
    }
}

#[derive(Clone)]
pub struct Global<T> {
    pub value: T,
    pub info: Arc<OptimizerInfo>,
}

#[derive(Default)]
pub struct OptimizerInfo {
    pub local_bindings: FnvMap<Symbol, Binding<CoreExpr, CoreClosure>>,
    pub pure_symbols: PurityMap,
    pub costs: Costs,
}

impl<T> Eq for Global<T> where T: Eq {}

impl<T> PartialEq for Global<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T> Hash for Global<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.value.hash(h)
    }
}

impl<T> fmt::Display for Global<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl<T> fmt::Debug for Global<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

type ReducedExpr<'l> = Reduced<CExpr<'l>, Global<CoreExpr>>;

trait Resolver<'l, 'a> {
    fn produce(&mut self, expr: CExpr<'a>) -> CExpr<'l>;
    fn produce_slice(&mut self, expr: &'a [Expr<'a>]) -> &'l [Expr<'l>];
    fn wrap(&self, expr: CExpr<'a>) -> ReducedExpr<'l>;
    fn find(&self, s: &Symbol) -> Option<GlobalBinding>;
    fn cost(&self, s: &SymbolRef) -> Cost;
}

impl<'a> Resolver<'a, 'a> for SameLifetime<'a> {
    fn produce(&mut self, expr: CExpr<'a>) -> CExpr<'a> {
        expr
    }
    fn produce_slice(&mut self, expr: &'a [Expr<'a>]) -> &'a [Expr<'a>] {
        expr
    }
    fn wrap(&self, expr: CExpr<'a>) -> ReducedExpr<'a> {
        Reduced::Local(expr)
    }
    fn find(&self, _: &Symbol) -> Option<GlobalBinding> {
        None
    }
    fn cost(&self, _: &SymbolRef) -> Cost {
        Cost::max_value()
    }
}

struct Different<'l, 'g, 'a, F> {
    producer: DifferentLifetime<'l, 'g>,
    info: &'a Arc<OptimizerInfo>,
    make_expr: F,
}
impl<'l, 'b, 'a, F> Resolver<'l, 'b> for Different<'l, 'b, 'a, F>
where
    F: Fn(CExpr<'b>) -> CoreExpr,
{
    fn produce(&mut self, expr: CExpr<'b>) -> CExpr<'l> {
        self.producer.produce(expr)
    }
    fn produce_slice(&mut self, expr: &'b [Expr<'b>]) -> &'l [Expr<'l>] {
        self.producer.produce_slice(expr)
    }
    fn wrap(&self, expr: CExpr<'b>) -> ReducedExpr<'l> {
        Reduced::Global(Global {
            info: self.info.clone(),
            value: (self.make_expr)(expr),
        })
    }
    fn find(&self, s: &Symbol) -> Option<GlobalBinding> {
        self.info.local_bindings.get(s).map(|bind| match bind {
            Binding::Expr(expr) => Binding::Expr(Global {
                info: self.info.clone(),
                value: expr.clone(),
            }),
            Binding::Closure(closure) => Binding::Closure(Global {
                info: self.info.clone(),
                value: closure.clone(),
            }),
        })
    }
    fn cost(&self, s: &SymbolRef) -> Cost {
        self.info.costs.cost(s)
    }
}

impl<'l> ReducedExpr<'l> {
    fn into_local(self, allocator: &'l Allocator<'l>) -> CExpr<'l> {
        match self {
            Reduced::Local(e) => e,
            Reduced::Global(e) => DifferentLifetime::new(allocator).produce(e.value.expr()),
        }
    }

    fn as_ref(&self) -> &Expr {
        match self {
            Reduced::Local(e) => e,
            Reduced::Global(e) => e.value.expr(),
        }
    }

    fn with<R>(
        self,
        allocator: &'l Allocator<'l>,
        f: impl for<'a> FnOnce(&mut dyn Resolver<'l, 'a>, CExpr<'a>) -> R,
    ) -> R {
        match self {
            Reduced::Local(expr) => f(&mut SameLifetime::new(allocator), expr),
            Reduced::Global(global) => {
                let info = &global.info;
                global.value.with(|make_expr, _, expr| {
                    f(
                        &mut Different {
                            producer: DifferentLifetime::new(allocator),
                            info,
                            make_expr,
                        },
                        expr,
                    )
                })
            }
        }
    }
}

impl<'l> ReducedClosure<'l> {
    fn with<R>(
        self,
        allocator: &'l Allocator<'l>,
        f: impl for<'a> FnOnce(
            &mut dyn Resolver<'l, 'a>,
            (&TypedIdent<Symbol>, &[TypedIdent<Symbol>], ReducedExpr<'l>),
        ) -> R,
    ) -> R {
        match &self {
            Reduced::Local(_) => f(&mut SameLifetime::new(allocator), self.as_ref()),
            Reduced::Global(global) => {
                let info = &global.info;
                global.value.clone().with(|make_expr, _, _| {
                    f(
                        &mut Different {
                            producer: DifferentLifetime::new(allocator),
                            info,
                            make_expr,
                        },
                        self.as_ref(),
                    )
                })
            }
        }
    }
}

impl<'l> From<CExpr<'l>> for ReducedExpr<'l> {
    fn from(expr: CExpr<'l>) -> Self {
        Reduced::Local(expr)
    }
}

enum Tail<'a> {
    Let {
        bind: &'a LetBinding<'a>,
        new_bind: Option<&'a LetBinding<'a>>,
        body: CExpr<'a>,
    },
    Match {
        expr: CExpr<'a>,
        new_expr: Option<CExpr<'a>>,
        alt: &'a Alternative<'a>,
    },
}
enum TailCall<'a, T> {
    Tail(CExpr<'a>),
    Value(T),
}

type ReducedClosure<'l> = Reduced<ClosureRef<'l>, Global<CoreClosure>>;

impl<'l, 'g> ReducedClosure<'l> {
    fn as_ref(&self) -> (&TypedIdent<Symbol>, &[TypedIdent<Symbol>], ReducedExpr<'l>) {
        match self {
            Reduced::Local(ClosureRef { id, args, body }) => (id, args, Reduced::Local(body)),
            Reduced::Global(c) => (
                c.value.closure().id,
                c.value.closure().args,
                Reduced::Global(Global {
                    info: c.info.clone(),
                    value: c.value.clone().into_expr(),
                }),
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binding<E, C> {
    Expr(E),
    Closure(C),
}

impl<E, C> fmt::Display for Binding<E, C>
where
    E: fmt::Display,
    C: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Binding::Expr(e) => e.fmt(f),
            Binding::Closure(e) => e.fmt(f),
        }
    }
}

impl<'l, 'g, C> From<ReducedExpr<'l>> for Binding<ReducedExpr<'l>, C> {
    fn from(expr: ReducedExpr<'l>) -> Self {
        Binding::Expr(expr)
    }
}

impl<'l, 'g, E> From<ReducedClosure<'l>> for Binding<E, ReducedClosure<'l>> {
    fn from(expr: ReducedClosure<'l>) -> Self {
        Binding::Closure(expr)
    }
}

impl<E, C> Binding<E, C> {
    fn as_expr(&self) -> Option<&E> {
        match self {
            Binding::Expr(e) => Some(e),
            Binding::Closure(_) => None,
        }
    }
}

type StackBinding<'l> = Binding<ReducedExpr<'l>, ReducedClosure<'l>>;

#[derive(Clone, Debug)]
struct CostBinding<'l> {
    cost: Cost,
    bind: StackBinding<'l>,
}

pub struct Pure<'a, 'l: 'a, 'g: 'a>(bool, &'a Compiler<'g, 'l>);

impl<'a, 'l, 'g, 'expr> Visitor<'l, 'expr> for Pure<'a, 'l, 'g> {
    type Producer = DifferentLifetime<'l, 'expr>;

    fn visit_expr(&mut self, expr: CExpr<'expr>) -> Option<CExpr<'l>> {
        if !self.0 {
            return None;
        }
        match *expr {
            Expr::Call(f, _) => {
                match *f {
                    Expr::Ident(ref id, ..) => {
                        match self.1.find(&id.name) {
                            Some(variable) => match &variable.bind {
                                Binding::Expr(expr) => {
                                    self.visit_expr(expr.as_ref());
                                }
                                Binding::Closure(closure) => {
                                    self.visit_expr(closure.as_ref().2.as_ref());
                                }
                            },
                            // If we can't resolve the identifier to an expression it is a
                            // primitive function which can be impure
                            // FIXME Let primitive functions mark themselves as pure somehow
                            None => {
                                if !id.name.as_ref().starts_with("#") {
                                    self.0 = false;
                                }
                            }
                        }
                    }
                    _ => self.0 = false,
                }
                walk_expr_alloc(self, expr)
            }
            Expr::Let(ref bind, expr) => {
                match bind.expr {
                    // Creating a group of closures is always pure (though calling them may not be)
                    Named::Recursive(_) => (),
                    Named::Expr(expr) => {
                        self.visit_expr(expr);
                    }
                }
                self.visit_expr(expr)
            }
            _ => walk_expr_alloc(self, expr),
        }
    }
    fn detach_allocator(&self) -> Option<&'l Allocator<'l>> {
        None
    }
}

fn is_pure(compiler: &Compiler, expr: CExpr) -> bool {
    let mut v = Pure(true, compiler);
    v.visit_expr(expr);
    v.0
}

struct FunctionEnv<'l, 'g> {
    _marker: PhantomData<(&'l (), &'g ())>,
}

struct FunctionEnvs<'l, 'g> {
    envs: Vec<FunctionEnv<'l, 'g>>,
}

impl<'l, 'g> Deref for FunctionEnvs<'l, 'g> {
    type Target = FunctionEnv<'l, 'g>;
    fn deref(&self) -> &FunctionEnv<'l, 'g> {
        self.envs.last().expect("FunctionEnv")
    }
}

impl<'l, 'g> DerefMut for FunctionEnvs<'l, 'g> {
    fn deref_mut(&mut self) -> &mut FunctionEnv<'l, 'g> {
        self.envs.last_mut().expect("FunctionEnv")
    }
}

impl<'l, 'g> FunctionEnvs<'l, 'g> {
    fn new() -> FunctionEnvs<'l, 'g> {
        FunctionEnvs { envs: vec![] }
    }

    fn start_function(&mut self, compiler: &mut Compiler) {
        compiler.stack_types.enter_scope();
        compiler.stack_constructors.enter_scope();
        self.envs.push(FunctionEnv::new());
    }

    fn end_function(&mut self, compiler: &mut Compiler) -> FunctionEnv<'l, 'g> {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl<'l, 'g> FunctionEnv<'l, 'g> {
    fn new() -> FunctionEnv<'l, 'g> {
        FunctionEnv {
            _marker: Default::default(),
        }
    }
}

pub type GlobalBinding = Binding<Global<CoreExpr>, Global<CoreClosure>>;

pub struct Compiler<'a, 'e> {
    allocator: &'e Allocator<'e>,
    globals: &'a dyn Fn(&Symbol) -> Option<GlobalBinding>,
    local_bindings: FnvMap<Symbol, Option<CostBinding<'e>>>,
    bindings_in_scope: ScopedMap<Symbol, ()>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
    costs: core::costs::Costs,
    pure_symbols: Option<&'a PurityMap>,
    bindings: Vec<Tail<'e>>,
}

impl<'a, 'e> KindEnv for Compiler<'a, 'e> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl<'a, 'e> TypeEnv for Compiler<'a, 'e> {
    type Type = ArcType;

    fn find_type(&self, _id: &SymbolRef) -> Option<ArcType> {
        None
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        self.stack_types.get(id).cloned()
    }
}

impl<'a, 'e> Compiler<'a, 'e> {
    pub fn new(
        allocator: &'e Allocator<'e>,
        globals: &'a dyn Fn(&Symbol) -> Option<GlobalBinding>,
    ) -> Compiler<'a, 'e> {
        Compiler {
            allocator,
            globals,
            local_bindings: FnvMap::default(),
            bindings_in_scope: ScopedMap::default(),
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
            costs: Default::default(),
            pure_symbols: Default::default(),
            bindings: Vec::new(),
        }
    }

    pub fn optimizer_info(self, allocator: &'e Arc<Allocator<'e>>) -> OptimizerInfo {
        OptimizerInfo {
            local_bindings: self
                .local_bindings
                .into_iter()
                .map(|(key, value)| {
                    (
                        key,
                        match value.as_ref().map(|b| &b.bind) {
                            Some(Binding::Expr(Reduced::Local(expr))) => {
                                Some(Binding::Expr(crate::core::freeze_expr(allocator, expr)))
                            }
                            Some(Binding::Closure(Reduced::Local(ClosureRef {
                                id,
                                args,
                                body,
                            }))) => Some(Binding::Closure(crate::core::freeze_closure(
                                allocator, id, args, body,
                            ))),
                            _ => None,
                        },
                    )
                })
                .filter_map(|(key, opt)| opt.map(|value| (key.clone(), value)))
                .collect(),
            pure_symbols: self.pure_symbols.cloned().unwrap_or_default(),
            costs: self.costs,
        }
    }

    pub fn costs(mut self, costs: core::costs::Costs) -> Self {
        self.costs = costs;
        self
    }

    pub fn pure_symbols(mut self, pure_symbols: &'a PurityMap) -> Self {
        self.pure_symbols = Some(pure_symbols);
        self
    }

    fn push_unknown_stack_var(&mut self, s: Symbol) {
        self.bindings_in_scope.insert(s.clone(), ());
        self.local_bindings.insert(s, None);
    }

    fn push_stack_var(&mut self, s: Symbol, bind: Option<StackBinding<'e>>) {
        let bind = bind.and_then(|bind| {
            let is_closure = match bind {
                Binding::Closure(_) => true,
                Binding::Expr(_) => false,
            };
            if is_closure
                || self
                    .pure_symbols
                    .as_ref()
                    .map_or(false, |p| p.pure_load(&s))
            {
                Some(bind)
            } else {
                None
            }
        });
        self.bindings_in_scope.insert(s.clone(), ());

        let bind = bind.map(|bind| CostBinding {
            cost: self.costs.cost(&s),
            bind,
        });
        self.local_bindings.insert(s, bind);
    }

    fn push_inline_stack_var(&mut self, s: Symbol, bind: Option<StackBinding<'e>>) -> bool {
        let bind = bind.and_then(|bind| {
            let is_closure = match bind {
                Binding::Closure(_) => true,
                Binding::Expr(_) => false,
            };
            if is_closure
                || self
                    .pure_symbols
                    .as_ref()
                    .map_or(false, |p| p.pure_load(&s))
                || bind
                    .as_expr()
                    .map_or(false, |expr| is_pure(self, expr.as_ref()))
            {
                Some(bind)
            } else {
                None
            }
        });
        let added = bind.is_some();
        self.bindings_in_scope.insert(s.clone(), ());
        self.local_bindings
            .insert(s, bind.map(|bind| CostBinding { cost: 0, bind }));
        added
    }

    fn cost(&self, resolver: &dyn Resolver<'_, '_>, id: &SymbolRef) -> Cost {
        let cost = self.costs.cost(id);
        if cost == Cost::max_value() {
            resolver.cost(id)
        } else {
            cost
        }
    }

    fn find(&self, id: &Symbol) -> Option<CostBinding<'e>> {
        self.local_bindings
            .get(id)
            .cloned()
            .or_else(|| {
                Some((self.globals)(id).map(|global| CostBinding {
                    cost: 0,
                    bind: match global {
                        Binding::Expr(expr) => Binding::Expr(Reduced::Global(expr)),
                        Binding::Closure(c) => Binding::Closure(Reduced::Global(c)),
                    },
                }))
            })
            .and_then(|e| e)
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: CExpr<'e>) -> Result<CExpr<'e>> {
        let mut env = FunctionEnvs::new();

        env.start_function(self);
        debug!("Interpreting: {}", expr);
        let new_expr = self.compile(expr, &mut env);
        if let Some(new_expr) = new_expr {
            debug!("Interpreted to: {}", new_expr);
        }
        env.end_function(self);
        Ok(new_expr.unwrap_or(expr))
    }

    fn load_identifier(
        &self,
        _resolver: &dyn Resolver<'_, '_>,
        id: &Symbol,
    ) -> Option<CostBinding<'e>> {
        self.find(id).map(|bind| {
            if let Binding::Expr(e) = &bind.bind {
                debug!("Loading `{}` at `{}` as `{}`", id, bind.cost, e.as_ref());
            }
            bind
        })
    }

    fn walk_expr(
        &mut self,
        expr: CExpr<'e>,
        functions: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<Option<CExpr<'e>>> {
        struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
            compiler: &'f mut Compiler<'a, 'e>,
            functions: &'f mut FunctionEnvs<'e, 'a>,
            error: Option<Error>,
        }
        impl<'a, 'e, 'f> Visitor<'e, 'e> for ReplaceVisitor<'a, 'e, 'f> {
            type Producer = SameLifetime<'e>;

            fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                self.compiler.compile(expr, self.functions)
            }
            fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                Some(self.compiler.allocator)
            }
        }

        let mut visitor = ReplaceVisitor {
            compiler: self,
            functions,
            error: None,
        };
        let new_expr = walk_expr_alloc(&mut visitor, expr);
        match visitor.error {
            Some(err) => Err(err),
            None => Ok(new_expr),
        }
    }

    fn compile(
        &mut self,
        mut expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        let scope_start = self.bindings.len();
        loop {
            let tail = match self.compile_(expr, function) {
                Ok(x) => x,
                Err(err) => {
                    info!("{}", err);
                    return None;
                }
            };
            match tail {
                TailCall::Tail(tail) => expr = tail,
                TailCall::Value(mut value) => {
                    let allocator = self.allocator;
                    let optimized = self.optimize_top(&value.unwrap_or(expr), function);
                    if let Some(opt_expr) = optimized {
                        if !ptr::eq::<Expr>(opt_expr, expr) {
                            value = optimized;
                        }
                    }

                    for _ in scope_start..self.bindings.len() {
                        self.stack_constructors.exit_scope();
                        self.bindings_in_scope.exit_scope();
                    }

                    return self
                        .bindings
                        .drain(scope_start..)
                        .rev()
                        .fold(value, |value, tail| match tail {
                            Tail::Match {
                                expr,
                                new_expr,
                                alt,
                            } => {
                                let new_alt = value.map(|expr| {
                                    &*allocator.alternative_arena.alloc(Alternative {
                                        pattern: alt.pattern.clone(),
                                        expr,
                                    })
                                });
                                optimize::merge_match(
                                    allocator,
                                    expr,
                                    new_expr,
                                    slice::from_ref(alt),
                                    new_alt.map(slice::from_ref),
                                )
                            }
                            Tail::Let {
                                bind,
                                new_bind,
                                body,
                            } => merge(&bind, new_bind, &body, value, |bind, body| {
                                match &bind.expr {
                                    Named::Recursive(closures) if closures.is_empty() => body,
                                    _ => &*allocator.arena.alloc(Expr::Let(bind, body)),
                                }
                            }),
                        });
                }
            }
        }
    }

    fn compile_(
        &mut self,
        expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<TailCall<'e, Option<CExpr<'e>>>> {
        let reduced = match *expr {
            Expr::Const(_, _) | Expr::Ident(..) => None,
            Expr::Let(ref let_binding, ref body) => {
                self.stack_constructors.enter_scope();
                self.bindings_in_scope.enter_scope();
                let new_named = match let_binding.expr {
                    core::Named::Expr(ref bind_expr) => {
                        trace!("Optimizing {}", let_binding.name.name);
                        let reduced = self.compile(bind_expr, function);
                        if let Some(reduced) = &reduced {
                            trace!("Optimized to {}", reduced);
                        }
                        self.push_stack_var(
                            let_binding.name.name.clone(),
                            Some(
                                reduced
                                    .map(Reduced::Local)
                                    .unwrap_or(Reduced::Local(bind_expr))
                                    .into(),
                            ),
                        );
                        reduced.map(|e| Named::Expr(e))
                    }
                    core::Named::Recursive(ref closures) => {
                        for closure in closures.iter() {
                            trace!(
                                "Optimizing {} from \\{} -> {}",
                                closure.name.name,
                                closure.args.iter().map(|id| &id.name).format(" "),
                                closure.expr
                            );
                            self.push_stack_var(
                                closure.name.name.clone(),
                                Some(
                                    Reduced::Local(ClosureRef {
                                        id: &closure.name,
                                        args: &closure.args[..],
                                        body: closure.expr,
                                    })
                                    .into(),
                                ),
                            );
                        }
                        let mut result = Ok(());
                        let new_closures = merge_collect(
                            closures,
                            |closure| {
                                let new_body = match self.compile_lambda(
                                    &closure.name,
                                    &closure.args,
                                    &closure.expr,
                                    function,
                                ) {
                                    Ok(b) => b,
                                    Err(err) => {
                                        result = Err(err);
                                        return None;
                                    }
                                };
                                let new_body = new_body.map(|expr| {
                                    trace!(
                                        "Optimized {} to \\{} -> {}",
                                        closure.name.name,
                                        closure.args.iter().map(|id| &id.name).format(" "),
                                        expr
                                    );
                                    Closure {
                                        pos: closure.pos,
                                        name: closure.name.clone(),
                                        args: closure.args.clone(),
                                        expr: expr,
                                    }
                                });

                                new_body
                            },
                            Clone::clone,
                        )
                        .map(Named::Recursive);
                        result?;
                        new_closures
                    }
                };
                self.bindings.push(Tail::Let {
                    new_bind: new_named.map(|expr| {
                        &*self.allocator.let_binding_arena.alloc(LetBinding {
                            expr,
                            ..(*let_binding).clone()
                        })
                    }),
                    bind: let_binding,
                    body,
                });
                return Ok(TailCall::Tail(body));
            }

            Expr::Match(expr, alts) if alts.len() == 1 => {
                let new_expr = self.compile(expr, function);
                self.stack_constructors.enter_scope();

                self.bindings_in_scope.enter_scope();

                let alt = &alts[0];
                match alt.pattern {
                    Pattern::Constructor(_, ref args) => {
                        for arg in args.iter() {
                            self.push_unknown_stack_var(arg.name.clone());
                        }
                    }
                    Pattern::Record { .. } => {
                        let expr = self.peek_expr(expr);
                        self.compile_let_pattern(&alt.pattern, expr, function);
                    }
                    Pattern::Ident(ref id) => {
                        let expr = self.peek(expr);
                        self.push_stack_var(id.name.clone(), Some(expr));
                    }
                    Pattern::Literal(_) => (),
                }

                self.bindings.push(Tail::Match {
                    expr,
                    new_expr,
                    alt,
                });
                return Ok(TailCall::Tail(&alt.expr));
            }

            Expr::Match(expr, alts) => {
                let allocator = self.allocator;
                let new_expr = self.compile(expr, function);
                let new_alts = optimize::merge_slice(allocator, alts, |alt| {
                    self.stack_constructors.enter_scope();
                    self.bindings_in_scope.enter_scope();

                    match alt.pattern {
                        Pattern::Constructor(_, ref args) => {
                            for arg in args.iter() {
                                self.push_unknown_stack_var(arg.name.clone());
                            }
                        }
                        Pattern::Record { .. } => {
                            let expr = self.peek_expr(expr);
                            self.compile_let_pattern(&alt.pattern, expr, function);
                        }
                        Pattern::Ident(ref id) => {
                            let expr = self.peek(expr);
                            self.push_stack_var(id.name.clone(), Some(expr));
                        }
                        Pattern::Literal(_) => (),
                    }

                    let new_expr = self.compile(&alt.expr, function);

                    self.bindings_in_scope.exit_scope();
                    self.stack_constructors.exit_scope();

                    new_expr.map(|expr| Alternative {
                        pattern: alt.pattern.clone(),
                        expr,
                    })
                });
                optimize::merge_match(allocator, expr, new_expr, alts, new_alts)
            }
            Expr::Call(..) | Expr::Data(..) | Expr::Cast(..) => self.walk_expr(expr, function)?,
        };
        Ok(TailCall::Value(reduced))
    }

    fn contains_unbound_variables(&mut self, expr: CExpr<'_>) -> bool {
        struct CheckUnbound<'a>(&'a mut ScopedMap<Symbol, ()>, bool);
        impl<'a, 'e> Visitor<'e, 'e> for CheckUnbound<'a> {
            type Producer = SameLifetime<'e>;

            fn visit_binding(&mut self, id: &Symbol) -> Option<Symbol> {
                self.0.insert(id.clone(), ());
                None
            }

            fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                if self.1 {
                    return None;
                }
                match expr {
                    Expr::Ident(id, ..) => {
                        if !id.name.declared_name().starts_with('#')
                            && !id.name.is_global()
                            && !self.0.contains_key(&id.name)
                        {
                            self.1 = true;
                        }
                        None
                    }
                    Expr::Let(..) => {
                        self.0.enter_scope();
                        walk_expr_alloc(self, expr);
                        self.0.exit_scope();
                        None
                    }
                    Expr::Match(scrutinee, alts) => {
                        self.visit_expr(scrutinee);

                        for alt in *alts {
                            self.0.enter_scope();

                            self.visit_pattern(&alt.pattern);
                            self.visit_expr(alt.expr);

                            self.0.exit_scope();
                        }

                        None
                    }
                    _ => walk_expr_alloc(self, expr),
                }
            }
            fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                None
            }
        }

        let mut visitor = CheckUnbound(&mut self.bindings_in_scope, false);
        visitor.visit_expr(expr);
        visitor.1
    }

    fn optimize_top(
        &mut self,
        expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        let mut replaced_expr = Vec::new();
        let mut expr = Reduced::Local(expr);
        loop {
            let replaced_expr_len = replaced_expr.len();
            let new_expr = self
                .peek_reduced_expr_fn(expr.clone(), &mut |cost, e| {
                    replaced_expr.push((cost, e.clone()))
                })
                .with(
                    self.allocator,
                    |resolver, reduced_expr| -> Option<CExpr<'e>> {
                        match reduced_expr {
                            Expr::Call(..) => {
                                let (f, args) = split_call(reduced_expr);
                                self.inline_call(function, resolver, reduced_expr, f, args)
                            }
                            Expr::Ident(..) => self
                                .inline_call(
                                    function,
                                    resolver,
                                    reduced_expr,
                                    reduced_expr,
                                    [].iter(),
                                )
                                .or_else(|| {
                                    if !ptr::eq::<Expr>(expr.as_ref(), reduced_expr) {
                                        Some(resolver.produce(reduced_expr))
                                    } else {
                                        None
                                    }
                                }),
                            Expr::Const(..) if !ptr::eq::<Expr>(expr.as_ref(), reduced_expr) => {
                                Some(resolver.produce(reduced_expr))
                            }
                            _ => None,
                        }
                    },
                );

            match new_expr {
                None => {
                    if replaced_expr_len != replaced_expr.len() {
                        expr = replaced_expr.last().unwrap().clone().1;
                        continue;
                    }

                    return replaced_expr
                        .into_iter()
                        .rev()
                        .find(|(cost, e)| {
                            *cost <= 10 && !self.contains_unbound_variables(e.as_ref())
                        })
                        .map(|(_, e)| e.into_local(&self.allocator));
                }
                Some(e) => {
                    expr = Reduced::Local(e);
                    replaced_expr.push((0, Reduced::Local(e)));
                }
            }
        }
    }

    fn inline_call<'b>(
        &mut self,
        function: &mut FunctionEnvs<'e, 'a>,
        resolver: &mut dyn Resolver<'e, 'b>,
        expr: CExpr<'b>,
        f: CExpr<'b>,
        mut args: impl ExactSizeIterator<Item = &'b Expr<'b>> + Clone,
    ) -> Option<CExpr<'e>> {
        trace!("TRY INLINE {}", expr);
        let f2 = self.peek_reduced(resolver.wrap(f));
        match f2.bind {
            Binding::Expr(peek_f) => match peek_f.as_ref() {
                Expr::Ident(ref id, ..) => {
                    if id.name.as_ref().starts_with("#") && args.len() == 2 {
                        let l = resolver.wrap(args.next().unwrap());
                        let r = resolver.wrap(args.next().unwrap());
                        self.reduce_primitive_binop(expr, id, l, r)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Binding::Closure(closure) => {
                let (closure_id, closure_args, closure_body) = closure.as_ref();

                let cost = closure.clone().with(self.allocator, |resolver, _| {
                    self.cost(resolver, &*closure_id.name)
                });
                trace!("COST {}: {}", closure_id.name, cost);

                if cost > 20 || closure_args.len() > args.len() {
                    None
                } else {
                    function.start_function(self);
                    trace!("{} -- {}", closure_args.len(), args.len());
                    // FIXME Avoid doing into_local here somehow
                    let closure_body = closure_body.into_local(self.allocator);

                    let mut inline = true;

                    self.bindings_in_scope.enter_scope();

                    for (name, value) in closure_args
                        .iter()
                        .zip(args.by_ref().map(|arg| resolver.wrap(arg)))
                    {
                        if !self.push_inline_stack_var(name.name.clone(), Some(value.into())) {
                            // If we aren't able to inline all variables we can't inline (right
                            // now, it causes unbound variable errors due to variables of the
                            // inlined function not being replaced)
                            inline = false;
                            trace!("Could not inline argument {}", name.name);
                            break;
                        }
                    }

                    let expr = if inline {
                        self.compile(closure_body, function).map(|new_expr| {
                            let args = self
                                .allocator
                                .arena
                                .alloc_fixed(args.map(|e| resolver.produce(e).clone()));
                            let new_expr = if !args.is_empty() {
                                // TODO Avoid allocating args and cloning them after into the
                                // slice
                                self.allocator.arena.alloc(Expr::Call(new_expr, args))
                            } else {
                                new_expr
                            };
                            trace!("INLINED {} ==>> {}", expr, new_expr);
                            new_expr
                        })
                    } else {
                        None
                    };

                    self.bindings_in_scope.exit_scope();

                    function.end_function(self);
                    expr
                }
            }
        }
    }

    fn peek(&mut self, expr: CExpr<'e>) -> StackBinding<'e> {
        self.peek_reduced(Reduced::Local(expr)).bind
    }

    fn peek_expr(&mut self, expr: CExpr<'e>) -> ReducedExpr<'e> {
        self.peek_reduced_expr(Reduced::Local(expr))
    }

    fn peek_reduced_expr(&mut self, expr: ReducedExpr<'e>) -> ReducedExpr<'e> {
        match self.peek_reduced(expr.clone()).bind {
            Binding::Expr(expr) => expr,
            _ => expr,
        }
    }

    fn peek_reduced(&mut self, expr: ReducedExpr<'e>) -> CostBinding<'e> {
        self.peek_reduced_fn(expr, &mut |_, _| ())
    }

    fn peek_reduced_expr_fn(
        &mut self,
        mut expr: ReducedExpr<'e>,
        report_reduction: &mut dyn FnMut(Cost, &ReducedExpr<'e>),
    ) -> ReducedExpr<'e> {
        let b = self.peek_reduced_fn(expr.clone(), &mut |cost, new_expr| {
            expr = new_expr.clone();
            report_reduction(cost, new_expr)
        });
        match b.bind {
            Binding::Expr(expr) => expr,
            _ => expr,
        }
    }

    fn peek_reduced_fn(
        &mut self,
        mut expr: ReducedExpr<'e>,
        report_reduction: &mut dyn FnMut(Cost, &ReducedExpr<'e>),
    ) -> CostBinding<'e> {
        loop {
            let new_bind = expr.clone().with(self.allocator, |resolver, expr| {
                match peek_through_lets(expr) {
                    Expr::Ident(ref id, _) => {
                        self.load_identifier(resolver, &id.name).or_else(|| {
                            resolver.find(&id.name).map(|bind| match bind {
                                Binding::Expr(e) => CostBinding {
                                    cost: 0,
                                    bind: Binding::Expr(Reduced::Global(e)),
                                },
                                Binding::Closure(c) => CostBinding {
                                    cost: 0,
                                    bind: Binding::Closure(Reduced::Global(c)),
                                },
                            })
                        })
                    }
                    Expr::Match(match_expr, alts) if alts.len() == 1 => {
                        let alt = &alts[0];
                        match (&alt.pattern, &alt.expr) {
                            (Pattern::Record(fields), Expr::Ident(id, _))
                                if fields.len() == 1
                                    && id.name
                                        == *fields[0].1.as_ref().unwrap_or(&fields[0].0.name) =>
                            {
                                let field = &fields[0];
                                let match_expr = self.peek_reduced_expr(resolver.wrap(match_expr));
                                let projected =
                                    self.project_reduced(&field.0.name, match_expr.clone())?;
                                Some(CostBinding {
                                    cost: 0,
                                    bind: Binding::Expr(projected),
                                })
                            }
                            _ => None,
                        }
                    }
                    peek if !ptr::eq::<Expr>(peek, expr) => Some(CostBinding {
                        cost: 0,
                        bind: Binding::Expr(resolver.wrap(peek)),
                    }),
                    _ => None,
                }
            });

            match new_bind {
                Some(CostBinding {
                    cost,
                    bind: Binding::Expr(new_expr),
                }) => match (&new_expr, &expr) {
                    (Reduced::Local(l), Reduced::Local(r)) if ptr::eq::<Expr>(*l, *r) => {
                        return CostBinding {
                            cost,
                            bind: Binding::Expr(new_expr),
                        }
                    }
                    _ => {
                        expr = new_expr;
                        report_reduction(cost, &expr);
                    }
                },
                Some(bind) => return bind,
                None => {
                    return CostBinding {
                        cost: 0,
                        bind: Binding::Expr(expr),
                    }
                }
            }
        }
    }

    fn project_reduced(
        &mut self,
        symbol: &Symbol,
        expr: ReducedExpr<'e>,
    ) -> Option<ReducedExpr<'e>> {
        match self
            .peek_identifier(expr.clone())
            .map(|b| b.bind)
            .unwrap_or(Binding::Expr(expr.clone()))
        {
            Binding::Expr(expr) => expr.with(self.allocator, |resolver, expr| match expr {
                Expr::Data(id, fields, ..) => {
                    let (_, projected_expr) = id
                        .typ
                        .row_iter()
                        .zip(*fields)
                        .find(|(field, _)| field.name.declared_name() == symbol.declared_name())
                        .unwrap_or_else(|| ice!("Missing record field {} in {}", symbol, id.typ));
                    Some(resolver.wrap(projected_expr))
                }
                _ => None,
            }),
            _ => None,
        }
    }

    fn peek_identifier(&mut self, expr: ReducedExpr<'e>) -> Option<CostBinding<'e>> {
        trace!("Peek {}", expr);
        expr.with(self.allocator, |resolver, expr| {
            match peek_through_lets(expr) {
                Expr::Ident(id, ..) => Some(match self.load_identifier(resolver, &id.name) {
                    Some(bind) => bind,
                    None => match resolver.find(&id.name) {
                        // TODO Forward cost from find
                        Some(Binding::Expr(expr)) => CostBinding {
                            cost: 0,
                            bind: Binding::Expr(Reduced::Global(expr)),
                        },
                        Some(Binding::Closure(c)) => CostBinding {
                            cost: 0,
                            bind: Binding::Closure(Reduced::Global(c)),
                        },
                        None => return None,
                    },
                }),
                new_expr if !ptr::eq::<Expr>(expr, new_expr) => Some(CostBinding {
                    cost: 0,
                    bind: Binding::Expr(resolver.wrap(new_expr)),
                }),
                _ => None,
            }
        })
    }

    fn compile_let_pattern(
        &mut self,
        pattern: &Pattern,
        pattern_expr: ReducedExpr<'e>,
        _function: &mut FunctionEnvs<'e, 'a>,
    ) {
        let pattern_expr = pattern_expr.with(self.allocator, |resolver, expr| {
            resolver.wrap(peek_through_lets(expr))
        });
        trace!("### {}", pattern_expr);
        match *pattern {
            Pattern::Ident(ref name) => {
                self.push_stack_var(name.name.clone(), Some(pattern_expr.into()));
            }
            Pattern::Record(ref fields) => pattern_expr.with(
                self.allocator,
                |resolver, pattern_expr| match pattern_expr {
                    Expr::Data(ref data_id, ref exprs, _) => {
                        for pattern_field in fields {
                            let field = data_id
                                .typ
                                .row_iter()
                                .position(|field| field.name.name_eq(&pattern_field.0.name))
                                .expect("ICE: Record field does not exist");
                            let field_name = pattern_field
                                .1
                                .as_ref()
                                .unwrap_or(&pattern_field.0.name)
                                .clone();
                            let expr = Some(self.peek_reduced(resolver.wrap(&exprs[field])).bind);
                            self.push_stack_var(field_name, expr);
                        }
                    }
                    _ => {
                        for (id, _) in fields {
                            self.push_unknown_stack_var(id.name.clone());
                        }
                    }
                },
            ),
            Pattern::Constructor(..) => ice!("constructor pattern in let"),
            Pattern::Literal(..) => ice!("literal pattern in let"),
        }
    }

    fn compile_lambda(
        &mut self,
        id: &TypedIdent,
        args: &[TypedIdent],
        body: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<Option<CExpr<'e>>> {
        debug!(
            "Lambda {} {}",
            id.name,
            args.iter().map(|id| &id.name).format(" ")
        );
        function.start_function(self);

        self.bindings_in_scope.enter_scope();

        for arg in args {
            self.push_unknown_stack_var(arg.name.clone());
        }
        let body = self.compile(body, function);

        self.bindings_in_scope.exit_scope();

        function.end_function(self);
        Ok(body)
    }

    fn reduce_primitive_binop<'b>(
        &mut self,
        expr: CExpr<'b>,
        id: &TypedIdent<Symbol>,
        l: ReducedExpr<'e>,
        r: ReducedExpr<'e>,
    ) -> Option<CExpr<'e>> {
        macro_rules! binop {
            () => {{
                let f: fn(_, _) -> _ = match id.name.as_ref().chars().last().unwrap() {
                    '+' => |l, r| l + r,
                    '-' => |l, r| l - r,
                    '*' => |l, r| l * r,
                    '/' => |l, r| l / r,
                    _ => return None,
                };
                f
            }};
        }

        trace!("Fold binop {} {} {}", l, id.name, r);
        let l = self.peek_reduced_expr(l);
        let r = self.peek_reduced_expr(r);
        match (l.as_ref(), r.as_ref()) {
            (&Expr::Const(Literal::Int(l), ..), &Expr::Const(Literal::Int(r), ..)) => {
                let f = binop!();
                Some(
                    self.allocator
                        .arena
                        .alloc(Expr::Const(Literal::Int(f(l, r)), expr.span())),
                )
            }
            (&Expr::Const(Literal::Float(l), ..), &Expr::Const(Literal::Float(r), ..)) => {
                let f = binop!();
                Some(
                    self.allocator
                        .arena
                        .alloc(Expr::Const(Literal::Float(f(l, r)), expr.span())),
                )
            }
            _ => None,
        }
    }
}

fn split_call<'a>(
    mut expr: CExpr<'a>,
) -> (CExpr<'a>, impl ExactSizeIterator<Item = CExpr<'a>> + Clone) {
    #[derive(Clone)]
    struct ArgIter<'a>(CExpr<'a>, usize);

    impl<'a> Iterator for ArgIter<'a> {
        type Item = CExpr<'a>;
        fn next(&mut self) -> Option<Self::Item> {
            match self.0 {
                Expr::Call(f, args) => {
                    let i = self.1;
                    if i < args.len() {
                        self.1 += 1;
                        Some(&args[i])
                    } else {
                        self.0 = f;
                        self.1 = 0;
                        self.next()
                    }
                }
                _ => None,
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len();
            (len, Some(len))
        }
    }

    impl ExactSizeIterator for ArgIter<'_> {
        fn len(&self) -> usize {
            let mut len = 0;
            let mut expr = self.0;
            let mut used = self.1;
            loop {
                match expr {
                    Expr::Call(f, args) => {
                        if used < args.len() {
                            len += args.len() - used;
                            used = 0;
                        }
                        expr = f;
                    }
                    _ => return len,
                }
            }
        }
    }

    let iter = ArgIter(expr, 0);
    loop {
        expr = match expr {
            Expr::Call(f, _) => f,
            _ => return (expr, iter),
        }
    }
}

fn peek_through_lets(mut expr: CExpr) -> CExpr {
    loop {
        match *expr {
            Expr::Let(_, body) => expr = body,
            _ => break expr,
        }
    }
}

#[cfg(all(test, feature = "test"))]
pub(crate) mod tests {
    use super::*;

    use crate::base::{
        error::Errors,
        pos::{self, BytePos, Spanned},
        symbol::Symbols,
    };

    use crate::core::grammar::ExprParser;
    use crate::core::*;

    fn from_lalrpop<T, U>(
        err: lalrpop_util::ParseError<usize, T, U>,
    ) -> Spanned<Box<dyn::std::error::Error + Send + Sync>, BytePos>
    where
        T: fmt::Display,
        U: fmt::Display,
    {
        use lalrpop_util::ParseError::*;

        let (start, end) = match err {
            InvalidToken { location } => (location, location),
            UnrecognizedToken {
                token: (lpos, _, rpos),
                ..
            } => (lpos, rpos),
            UnrecognizedEOF { location, .. } => (location, location),
            ExtraToken {
                token: (lpos, _, rpos),
            } => (lpos, rpos),
            User { .. } => (Default::default(), Default::default()),
        };
        pos::spanned2(
            BytePos::from(start as u32),
            BytePos::from(end as u32),
            format!("{}", err).into(),
        )
    }

    pub fn parse_expr<'a>(
        symbols: &mut Symbols,
        allocator: &'a Allocator<'a>,
        expr_str: &str,
    ) -> CExpr<'a> {
        let actual_expr = ExprParser::new()
            .parse(symbols, &allocator, expr_str)
            .unwrap_or_else(|err| {
                let mut source = codespan::CodeMap::new();
                source.add_filemap("test".into(), expr_str.into());

                let mut errors = Errors::new();
                errors.push(from_lalrpop(err));

                panic!("{}", base::error::InFile::new(source, errors))
            });

        allocator.arena.alloc(actual_expr)
    }

    macro_rules! assert_eq_expr {
        ($actual:expr, $expected:expr) => {
            assert_eq_expr!($actual, $expected, |_: &Symbol| None)
        };
        ($actual:expr, $expected:expr, $globals:expr) => {{
            let mut symbols = Symbols::new();
            let globals = $globals;

            let allocator = Allocator::new();

            let actual_expr = parse_expr(&mut symbols, &allocator, $actual);

            let mut dep_graph = crate::core::dead_code::DepGraph::default();
            let used_bindings = dep_graph.used_bindings(actual_expr);

            let pure_symbols = crate::core::purity::purity(actual_expr);

            let actual_expr = crate::core::dead_code::dead_code_elimination(
                &used_bindings,
                &pure_symbols,
                &allocator,
                actual_expr,
            );

            let cyclic_bindings: FnvSet<_> = dep_graph.cycles().flat_map(|cycle| cycle).collect();

            let costs = crate::core::costs::analyze_costs(&cyclic_bindings, actual_expr);

            let actual_expr = {
                Compiler::new(&allocator, &globals)
                    .costs(costs)
                    .pure_symbols(&pure_symbols)
                    .compile_expr(actual_expr)
                    .unwrap()
            };

            let mut dep_graph = crate::core::dead_code::DepGraph::default();
            let used_bindings = dep_graph.used_bindings(actual_expr);
            let actual_expr = crate::core::dead_code::dead_code_elimination(
                &used_bindings,
                &pure_symbols,
                &allocator,
                actual_expr,
            );

            let expected_expr = parse_expr(&mut symbols, &allocator, $expected);

            assert_deq!(actual_expr, expected_expr);
        }};
    }

    #[test]
    fn fold_constant_variable() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in x ", " 1 ");
    }

    #[test]
    fn fold_multiple_constant_variables() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in let y = x in y ", " 1 ");
    }

    #[test]
    fn fold_record_pattern_match() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in match { x } with | { x } -> x end", "1");
    }

    #[test]
    fn dont_remove_let_that_cant_be_folded() {
        let _ = ::env_logger::try_init();

        let expr = r#"
        let x = f 1 in
        x"#;
        assert_eq_expr!(expr, expr);
    }

    #[test]
    fn fold_global() {
        let _ = ::env_logger::try_init();

        let global = with_allocator(|global_alloc| {
            crate::core::freeze_expr(
                global_alloc,
                global_alloc
                    .arena
                    .alloc(Expr::Const(Literal::Int(1), Span::default())),
            )
        });

        let expr = r#"
        x"#;
        assert_eq_expr!(expr, "1", move |_: &_| Some(Binding::Expr(Global {
            info: Default::default(),
            value: global.clone(),
        })));
    }

    #[test]
    fn fold_primitive_op() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            (#Int+) 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_function_call_basic() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x y = (#Int+) x y
            in f 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_function_call_with_unknown_parameters() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x y = (#Int+) x y in
            rec let g y = f 2 y in
            g
        "#;
        assert_eq_expr!(
            expr,
            r#"
            rec let g y = (#Int+) 2 y in
            g
        "#
        );
    }

    #[test]
    fn fold_extra_arguments() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let g x y = (#Int+) x y in
            rec let f x = g x
            in f 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_function_call_implicit() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let add_ l r = (#Int+) l r in
            let adder = { add = add_ } in
            rec let f a = a.add
            in f adder 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_applicative() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let apply app = app.apply in

            rec let apply2 app2 = apply app2 in

            rec let left_apply app3 l r = apply2 app3 (@unknown l) r

            in { left_apply }
        "#;
        let expected = r#"
            rec let apply app = app.apply in

            rec let left_apply app3 l r = (apply app3) (@unknown l) r

            in { left_apply }
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn abort_on_self_recursive_function() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x = f x
            in f
        "#;
        let expected = r#"
            rec let f x = f x
            in f
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn abort_on_indirect_self_recursive_function() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x = g x
            rec let g x = f x
            in f
        "#;
        let expected = r#"
            rec let f x = g x
            rec let g x = f x
            in f
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn match_record_elimination() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            let match_pattern = m state 
            in
            match match_pattern with
            | { value } -> value
            end
        "#;
        let expected = r#"
            let match_pattern = m state 
            in
            match match_pattern with
            | { value } -> value
            end
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn dont_duplicate_unknown_call_1() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let id x = x
            in
            rec let f g =
                let x = id g 123
                in x
            in f
        "#;
        let expected = r#"
            rec let id x = x
            in
            rec let f g =
                let x = id g 123
                in x
            in f
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn dont_duplicate_unknown_call_2() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let id x = x
            in
            rec let f g =
                let x = id g 123
                in
                match x with
                | y -> y
                end
            in f
        "#;
        let expected = r#"
            rec let id x = x
            in
            rec let f g =
                let x = id g 123
                in
                match x with
                | y -> y
                end
            in f
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn match_record_nested_match() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let r1 x =
                match { x = x } with
                | { x = p } ->
                    match p with
                    | 1 -> 11
                    | 2 -> 22
                    | _ -> 33
                    end
                end
            in r1 2
        "#;
        let expected = r#"
        match 2 with
        | 1 -> 11
        | 2 -> 22
        | _ -> 33
        end
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[test]
    fn fold_global_function_call_with_unknown_parameters() {
        let _ = ::env_logger::try_init();
        let mut symbols = Symbols::new();
        let mut pure_symbols = None;
        let mut costs = Default::default();
        let global = with_allocator(|global_allocator| {
            let expr = ExprParser::new()
                .parse(
                    &mut symbols,
                    &global_allocator,
                    "rec let f x y = (#Int+) x y in { f }",
                )
                .unwrap_or_else(|err| panic!("{}", err));
            pure_symbols = Some(crate::core::purity::purity(&expr));

            let mut dep_graph = dead_code::DepGraph::default();
            let _: Vec<_> = dep_graph.used_bindings(&expr);
            let cyclic_bindings: FnvSet<_> = dep_graph.cycles().flat_map(|cycle| cycle).collect();

            costs = crate::core::costs::analyze_costs(&cyclic_bindings, &expr);
            crate::core::freeze_expr(global_allocator, global_allocator.arena.alloc(expr))
        });

        let expr = r#"
            rec let g y = global.f 2 y in
            g
        "#;

        let info = Arc::new(OptimizerInfo {
            local_bindings: vec![(
                symbols.simple_symbol("f"),
                global
                    .clone()
                    .with(|_, make_closure, global| match *global {
                        Expr::Let(ref bind, _) => match bind.expr {
                            Named::Recursive(ref closures) => Binding::Closure(make_closure(
                                &closures[0].name,
                                &closures[0].args[..],
                                closures[0].expr,
                            )),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }),
            )]
            .into_iter()
            .collect(),
            pure_symbols: pure_symbols.unwrap(),
            costs: costs,
        });
        let f = move |s: &Symbol| match s.as_ref() {
            "global" => Some(Binding::Expr(Global {
                info: info.clone(),
                value: global.clone(),
            })),
            _ => None,
        };
        assert_eq_expr!(
            expr,
            r#"
                rec let g y = (#Int+) 2 y in
                g
            "#,
            f
        );
    }
}
