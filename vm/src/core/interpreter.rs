use std::{
    cell::RefCell,
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
    fnv::{FnvMap, FnvSet},
    kind::{ArcKind, KindEnv},
    merge::{merge_collect, merge_fn},
    pos::{BytePos, Span},
    scoped_map::ScopedMap,
    symbol::{Symbol, SymbolData, SymbolRef},
    types::{Alias, ArcType, TypeEnv, TypeExt},
};

use crate::core::{
    self,
    costs::{self, Cost, Costs},
    optimize::{
        self, walk_expr, walk_expr_alloc, DifferentLifetime, ExprProducer, OptimizeEnv,
        SameLifetime, Visitor,
    },
    purity::PurityMap,
    Allocator, Alternative, ArenaExt, CExpr, Closure, ClosureRef, CoreClosure, CoreExpr, Expr,
    LetBinding, Literal, Named, Pattern,
};

#[derive(Copy, Clone, Debug)]
pub enum Reduced<L, G> {
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

type OwnedReduced<T> = Reduced<T, Global<T>>;

#[derive(Debug, Default)]
pub struct OptimizerInfo {
    pub local_bindings: FnvMap<Symbol, OptimizerBinding>,
    pub pure_symbols: PurityMap,
    pub costs: Costs,
}

impl<T> Global<T> {
    fn new(info: &Arc<OptimizerInfo>, value: Reduced<T, Global<T>>) -> Global<T> {
        match value {
            Reduced::Local(value) => Global {
                value,
                info: info.clone(),
            },
            Reduced::Global(value) => value,
        }
    }
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
type ReducedClosure<'l> = Reduced<ClosureRef<'l>, Global<CoreClosure>>;
type StackBinding<'l> = Binding<ReducedExpr<'l>, ReducedClosure<'l>>;

pub type OptimizerBinding = Binding<OwnedReduced<CoreExpr>, OwnedReduced<CoreClosure>>;
pub type GlobalBinding = Binding<Global<CoreExpr>, Global<CoreClosure>>;

trait Resolver<'l, 'a> {
    fn produce(&self, expr: CExpr<'a>) -> CExpr<'l>;
    fn produce_slice(&self, expr: &'a [Expr<'a>]) -> &'l [Expr<'l>];
    fn produce_alts(&self, expr: &'a [Alternative<'a>]) -> &'l [Alternative<'l>];
    fn wrap(&self, expr: CExpr<'a>) -> ReducedExpr<'l>;
    fn wrap_closure(&self, closure: ClosureRef<'a>) -> ReducedClosure<'l>;
    fn find(&self, s: &Symbol) -> Option<GlobalBinding>;
    fn cost(&self, s: &SymbolRef) -> Cost;
    fn pure_load(&self, s: &SymbolRef) -> bool;
}

impl<'a> Resolver<'a, 'a> for SameLifetime<'a> {
    fn produce(&self, expr: CExpr<'a>) -> CExpr<'a> {
        expr
    }
    fn produce_slice(&self, expr: &'a [Expr<'a>]) -> &'a [Expr<'a>] {
        expr
    }
    fn produce_alts(&self, alt: &'a [Alternative<'a>]) -> &'a [Alternative<'a>] {
        alt
    }
    fn wrap(&self, expr: CExpr<'a>) -> ReducedExpr<'a> {
        Reduced::Local(expr)
    }
    fn wrap_closure(&self, closure: ClosureRef<'a>) -> ReducedClosure<'a> {
        Reduced::Local(closure)
    }
    fn find(&self, _: &Symbol) -> Option<GlobalBinding> {
        None
    }
    fn cost(&self, _: &SymbolRef) -> Cost {
        Cost::max_value()
    }
    fn pure_load(&self, _s: &SymbolRef) -> bool {
        false
    }
}

struct Different<'l, 'a, F, G> {
    allocator: &'l Allocator<'l>,
    info: &'a Arc<OptimizerInfo>,
    inlined_global_bindings: &'a RefCell<FnvMap<Symbol, Option<CostBinding<'l>>>>,
    make_expr: F,
    make_closure: G,
}
impl<'l, 'b, 'a, F, G> Resolver<'l, 'b> for Different<'l, 'a, F, G>
where
    F: Fn(CExpr<'b>) -> CoreExpr,
    G: Fn(ClosureRef<'b>) -> CoreClosure,
{
    fn produce(&self, expr: CExpr<'b>) -> CExpr<'l> {
        IntoLocal {
            allocator: self.allocator,
            info: &self.info,
            inlined_global_bindings: &self.inlined_global_bindings,
            _marker: PhantomData,
        }
        .produce(expr)
    }
    fn produce_slice(&self, expr: &'b [Expr<'b>]) -> &'l [Expr<'l>] {
        IntoLocal {
            allocator: self.allocator,
            info: &self.info,
            inlined_global_bindings: &self.inlined_global_bindings,
            _marker: PhantomData,
        }
        .produce_slice(expr)
    }
    fn produce_alts(&self, alts: &'b [Alternative<'b>]) -> &'l [Alternative<'l>] {
        self.allocator
            .alloc_iter(alts.iter().map(|alt| Alternative {
                pattern: alt.pattern.clone(),
                expr: self.produce(alt.expr),
            }))
    }
    fn wrap(&self, expr: CExpr<'b>) -> ReducedExpr<'l> {
        Reduced::Global(Global {
            info: self.info.clone(),
            value: (self.make_expr)(expr),
        })
    }
    fn wrap_closure(&self, closure: ClosureRef<'b>) -> ReducedClosure<'l> {
        Reduced::Global(Global {
            info: self.info.clone(),
            value: (self.make_closure)(closure),
        })
    }
    fn find(&self, s: &Symbol) -> Option<GlobalBinding> {
        self.info.local_bindings.get(s).map(|bind| match bind {
            Binding::Expr(expr) => Binding::Expr(Global::new(&self.info, expr.clone())),
            Binding::Closure(closure) => Binding::Closure(Global::new(&self.info, closure.clone())),
        })
    }
    fn cost(&self, s: &SymbolRef) -> Cost {
        self.info.costs.cost(s)
    }
    fn pure_load(&self, s: &SymbolRef) -> bool {
        self.info.pure_symbols.pure_load(s)
    }
}

#[derive(Clone)]
struct IntoLocal<'l, 'b> {
    allocator: &'l Allocator<'l>,
    info: &'b Arc<OptimizerInfo>,
    inlined_global_bindings: &'b RefCell<FnvMap<Symbol, Option<CostBinding<'l>>>>,
    _marker: PhantomData<&'b ()>,
}

impl<'l, 'b, 'r> Visitor<'l, 'r> for IntoLocal<'l, 'b> {
    type Producer = IntoLocal<'l, 'b>;

    fn visit_expr(&mut self, expr: &'r Expr<'r>) -> Option<&'l Expr<'l>> {
        Some(self.produce(expr))
    }

    fn producer(&self) -> Self::Producer {
        self.clone()
    }

    fn detach_allocator(&self) -> Option<&'l Allocator<'l>> {
        Some(self.allocator)
    }
}

impl<'l, 'b, 'r> ExprProducer<'l, 'r> for IntoLocal<'l, 'b> {
    fn new(_allocator: &'l Allocator<'l>) -> Self {
        unreachable!()
    }
    fn produce(&mut self, expr: CExpr<'r>) -> CExpr<'l> {
        match *expr {
            Expr::Const(ref id, ref span) => self
                .allocator
                .arena
                .alloc(Expr::Const(id.clone(), span.clone())),
            Expr::Ident(ref id, ref span) => {
                if let Some(bind) = self.info.local_bindings.get(&id.name) {
                    self.inlined_global_bindings.borrow_mut().insert(
                        id.name.clone(),
                        Some(CostBinding {
                            cost: 1,
                            bind: match bind {
                                Binding::Expr(expr) => Binding::Expr(Reduced::Global(Global::new(
                                    &self.info,
                                    expr.clone(),
                                ))),
                                Binding::Closure(c) => Binding::Closure(Reduced::Global(
                                    Global::new(&self.info, c.clone()),
                                )),
                            },
                        }),
                    );
                }
                self.allocator
                    .arena
                    .alloc(Expr::Ident(id.clone(), span.clone()))
            }
            Expr::Data(ref id, args, pos) if args.is_empty() => self
                .allocator
                .arena
                .alloc(Expr::Data(id.clone(), &[], pos.clone())),
            _ => walk_expr_alloc(self, expr).unwrap(),
        }
    }
    fn produce_slice(&mut self, exprs: &'r [Expr<'r>]) -> &'l [Expr<'l>] {
        self.allocator
            .arena
            .alloc_fixed(exprs.iter().map(|expr| match *expr {
                Expr::Const(ref id, ref span) => Expr::Const(id.clone(), span.clone()),
                Expr::Ident(ref id, ref span) => Expr::Ident(id.clone(), span.clone()),
                Expr::Data(ref id, args, pos) if args.is_empty() => {
                    Expr::Data(id.clone(), &[], pos.clone())
                }
                _ => walk_expr(self, expr).unwrap(),
            }))
    }
    fn produce_alt(&mut self, alt: &'r Alternative<'r>) -> Alternative<'l> {
        Alternative {
            pattern: alt.pattern.clone(),
            expr: self.produce(alt.expr),
        }
    }
    fn allocator(&self) -> &'l Allocator<'l> {
        self.allocator
    }
}

impl<'l> ReducedExpr<'l> {
    fn into_local(
        self,
        inlined_global_bindings: &RefCell<FnvMap<Symbol, Option<CostBinding<'l>>>>,
        allocator: &'l Allocator<'l>,
    ) -> CExpr<'l> {
        match self {
            Reduced::Local(e) => e,
            Reduced::Global(e) => IntoLocal {
                allocator,
                info: &e.info,
                inlined_global_bindings,
                _marker: PhantomData,
            }
            .produce(e.value.expr()),
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
        inlined_global_bindings: &RefCell<FnvMap<Symbol, Option<CostBinding<'l>>>>,
        f: impl for<'a> FnOnce(&dyn Resolver<'l, 'a>, CExpr<'a>) -> R,
    ) -> R {
        match self {
            Reduced::Local(expr) => f(&mut SameLifetime::new(allocator), expr),
            Reduced::Global(global) => {
                let info = &global.info;
                global.value.with(|make_expr, make_closure, expr| {
                    f(
                        &mut Different {
                            allocator,
                            info,
                            inlined_global_bindings,
                            make_expr,
                            make_closure,
                        },
                        expr,
                    )
                })
            }
        }
    }
}

impl<'l> ReducedClosure<'l> {
    #[allow(dead_code)]
    fn with<R>(
        self,
        allocator: &'l Allocator<'l>,
        inlined_global_bindings: &RefCell<FnvMap<Symbol, Option<CostBinding<'l>>>>,
        f: impl for<'a> FnOnce(
            &dyn Resolver<'l, 'a>,
            (&TypedIdent<Symbol>, &[TypedIdent<Symbol>], ReducedExpr<'l>),
        ) -> R,
    ) -> R {
        match &self {
            Reduced::Local(_) => f(&mut SameLifetime::new(allocator), self.as_ref()),
            Reduced::Global(global) => {
                let info = &global.info;
                global.value.clone().with(|make_expr, make_closure, _| {
                    let mut different = Different {
                        allocator,
                        info,
                        make_expr,
                        inlined_global_bindings,
                        make_closure,
                    };
                    f(&mut different, self.as_ref())
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

enum Tail<'l, 'a> {
    Let {
        bind: &'a LetBinding<'a>,
        new_bind: Option<&'l LetBinding<'l>>,
        body: CExpr<'a>,
    },
    Match {
        scrutinee_expr: CExpr<'a>,
        new_expr: Option<CExpr<'l>>,
        alt: &'a Alternative<'a>,
    },
}
enum TailCall<'l, 'a, T> {
    Tail(CExpr<'a>, Tail<'l, 'a>, CExpr<'a>),
    Value(T),
}

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

impl<'l, 'g, C> From<CExpr<'l>> for Binding<ReducedExpr<'l>, C> {
    fn from(expr: CExpr<'l>) -> Self {
        Binding::Expr(Reduced::Local(expr))
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

impl From<CoreExpr> for OptimizerBinding {
    fn from(expr: CoreExpr) -> Self {
        Binding::Expr(Reduced::Local(expr))
    }
}

impl From<CoreClosure> for OptimizerBinding {
    fn from(expr: CoreClosure) -> Self {
        Binding::Closure(Reduced::Local(expr))
    }
}

impl From<Global<CoreExpr>> for GlobalBinding {
    fn from(expr: Global<CoreExpr>) -> Self {
        Binding::Expr(expr)
    }
}

impl From<Global<CoreClosure>> for GlobalBinding {
    fn from(expr: Global<CoreClosure>) -> Self {
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

#[derive(Clone, Debug)]
pub(crate) struct CostBinding<'l> {
    cost: Cost,
    bind: StackBinding<'l>,
}

pub struct Pure<'a, 'l: 'a, 'g: 'a>(bool, &'a mut Compiler<'g, 'l>);

impl<'a, 'l, 'g, 'expr> Visitor<'l, 'expr> for Pure<'a, 'l, 'g> {
    type Producer = DifferentLifetime<'l, 'expr>;

    fn visit_expr(&mut self, expr: CExpr<'expr>) -> Option<CExpr<'l>> {
        if !self.0 {
            return None;
        }
        match *expr {
            Expr::Call(f, _) => {
                match *f {
                    Expr::Ident(ref id, ..)
                        if self
                            .1
                            .pure_symbols
                            .as_ref()
                            .map_or(false, |p| p.pure_call(&id.name)) =>
                    {
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
                                if !id.name.is_primitive() {
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

fn is_pure(compiler: &mut Compiler, expr: CExpr) -> bool {
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

pub(crate) struct Compiler<'a, 'e> {
    allocator: &'e Allocator<'e>,
    globals: &'a dyn Fn(&Symbol) -> Option<GlobalBinding>,
    #[allow(dead_code)]
    env: &'a dyn OptimizeEnv<Type = ArcType>,
    local_bindings: ScopedMap<Symbol, Option<CostBinding<'e>>>,
    all_local_bindings: FnvMap<Symbol, CostBinding<'e>>,
    inlined_global_bindings: &'a RefCell<FnvMap<Symbol, Option<CostBinding<'e>>>>,
    bindings_in_scope: ScopedMap<Symbol, ()>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
    costs: core::costs::Costs,
    cyclic_bindings: FnvSet<&'a SymbolRef>,
    pure_symbols: Option<&'a PurityMap>,
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
        env: &'a dyn OptimizeEnv<Type = ArcType>,
        inlined_global_bindings: &'a RefCell<FnvMap<Symbol, Option<CostBinding<'e>>>>,
    ) -> Compiler<'a, 'e> {
        Compiler {
            allocator,
            globals,
            env,
            local_bindings: Default::default(),
            all_local_bindings: Default::default(),
            inlined_global_bindings,
            bindings_in_scope: ScopedMap::default(),
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
            costs: Default::default(),
            cyclic_bindings: Default::default(),
            pure_symbols: Default::default(),
        }
    }

    pub fn optimizer_info(self, allocator: &'e Arc<Allocator<'e>>) -> OptimizerInfo {
        OptimizerInfo {
            local_bindings: self
                .all_local_bindings
                .into_iter()
                .map(|(k, v)| (k, Some(v)))
                .chain(self.inlined_global_bindings.borrow_mut().drain())
                .filter_map(|(key, value)| {
                    Some((
                        key,
                        match value.as_ref().map(|b| &b.bind) {
                            Some(Binding::Expr(Reduced::Local(expr))) => Binding::Expr(
                                Reduced::Local(crate::core::freeze_expr(allocator, expr)),
                            ),
                            Some(Binding::Closure(Reduced::Local(ClosureRef {
                                id,
                                args,
                                body,
                            }))) => Binding::Closure(Reduced::Local(crate::core::freeze_closure(
                                allocator, id, args, body,
                            ))),
                            Some(Binding::Expr(Reduced::Global(global))) => {
                                Binding::Expr(Reduced::Global(global.clone()))
                            }
                            Some(Binding::Closure(Reduced::Global(global))) => {
                                Binding::Closure(Reduced::Global(global.clone()))
                            }
                            None => return None,
                        },
                    ))
                })
                .collect(),
            pure_symbols: self.pure_symbols.cloned().unwrap_or_default(),
            costs: self.costs,
        }
    }

    pub fn costs(mut self, costs: core::costs::Costs) -> Self {
        self.costs = costs;
        self
    }

    pub fn cyclic_bindings(mut self, cyclic_bindings: FnvSet<&'a SymbolRef>) -> Self {
        self.cyclic_bindings = cyclic_bindings;
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

    fn remove_rename(&mut self, name: &Symbol) {
        if let Some(Some(CostBinding {
            bind: Binding::Expr(Reduced::Local(Expr::Ident(id, _))),
            ..
        })) = self.local_bindings.remove(name)
        {
            self.bindings_in_scope.remove(&id.name);
            let real_bind = self.local_bindings.remove(&id.name).unwrap();
            if let Some(bind) = &real_bind {
                self.all_local_bindings.insert(name.clone(), bind.clone());
            }
            self.local_bindings.insert(name.clone(), real_bind);
            let cost = self.costs.cost(&id.name);
            self.costs
                .insert(name.clone(), costs::Data { cost, uses: 0 });
        }
    }

    fn get_rename(&mut self, name: &Symbol) -> Symbol {
        match self
            .local_bindings
            .get(name)
            .unwrap_or_else(|| panic!("{} should have been inserted earlier", name))
        {
            Some(CostBinding {
                bind: Binding::Expr(Reduced::Local(Expr::Ident(name, _))),
                ..
            }) => name.name.clone(),
            Some(b) => unreachable!("{} {}", name, b.bind),
            None => unreachable!("{}", name),
        }
    }

    fn rename<'b>(&mut self, name: &TypedIdent<Symbol>, span: Span<BytePos>) -> Symbol {
        let data = name.name.as_data();
        let new_name = Symbol::from(SymbolData {
            global: data.global,
            location: data.location,
            name: &format!("{}_inl", data.name)[..],
        });
        let e = &*self.allocator.arena.alloc(Expr::Ident(
            TypedIdent {
                name: new_name.clone(),
                typ: name.typ.clone(),
            },
            span,
        ));
        let cost = match e {
            Expr::Ident(new_name, _) => {
                let cost = self.costs.cost(&name.name);
                self.costs
                    .insert(new_name.name.clone(), costs::Data { cost, uses: 0 });
                if self.cyclic_bindings.contains(&*name.name) {
                    self.cyclic_bindings.insert(&*new_name.name);
                    cost
                } else {
                    // This is just a load of a variable now
                    self.costs
                        .insert(name.name.clone(), costs::Data { cost: 1, uses: 0 });
                    1
                }
            }
            _ => unreachable!(),
        };

        self.bindings_in_scope.insert(name.name.clone(), ());
        let bind = Some(CostBinding {
            cost,
            bind: Reduced::Local(e).into(),
        });
        self.local_bindings.insert(name.name.clone(), bind);

        new_name
    }

    fn push_stack_var<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        s: Symbol,
        bind: Option<StackBinding<'e>>,
    ) {
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
                || resolver.pure_load(&s)
                || bind
                    .as_expr()
                    .map_or(false, |expr| is_pure(self, expr.as_ref()))
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
        if let Some(bind) = &bind {
            self.all_local_bindings.insert(s.clone(), bind.clone());
        }
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

    #[allow(dead_code)]
    fn cost(&self, resolver: &dyn Resolver<'_, '_>, id: &SymbolRef) -> Cost {
        let cost = self.costs.cost(id);
        if cost == Cost::max_value() {
            let cost = self
                .local_bindings
                .get(id)
                .and_then(|x| x.as_ref())
                .map(|b| b.cost)
                .unwrap_or_else(Cost::max_value);
            if cost == Cost::max_value() {
                resolver.cost(id)
            } else {
                cost
            }
        } else {
            cost
        }
    }

    fn find(&mut self, id: &Symbol) -> Option<CostBinding<'e>> {
        self.local_bindings
            .get(id)
            .cloned()
            .and_then(|e| e)
            .and_then(|bind| match &bind.bind {
                Binding::Expr(expr) => {
                    if self.contains_unbound_variables(&expr.as_ref()) {
                        None
                    } else {
                        Some(bind)
                    }
                }
                Binding::Closure(_) => Some(bind),
            })
            .or_else(|| {
                self.all_local_bindings
                    .get(id)
                    .cloned()
                    .and_then(|bind| match &bind.bind {
                        Binding::Expr(expr) => {
                            if self.contains_unbound_variables(&expr.as_ref()) {
                                None
                            } else {
                                Some(bind)
                            }
                        }
                        Binding::Closure(_) => Some(bind),
                    })
            })
            .or_else(|| {
                self.inlined_global_bindings
                    .borrow()
                    .get(id)
                    .cloned()
                    .and_then(|e| e)
            })
            .or_else(|| {
                (self.globals)(id)
                    .and_then(|global| match &global {
                        Binding::Expr(expr) => {
                            if self.contains_unbound_variables(&expr.value.expr()) {
                                None
                            } else {
                                Some(global)
                            }
                        }
                        Binding::Closure(_) => Some(global),
                    })
                    .map(|global| {
                        let bind = CostBinding {
                            cost: 1,
                            bind: match global {
                                Binding::Expr(expr) => Binding::Expr(Reduced::Global(expr)),
                                Binding::Closure(c) => Binding::Closure(Reduced::Global(c)),
                            },
                        };
                        self.inlined_global_bindings
                            .borrow_mut()
                            .insert(id.clone(), Some(bind.clone()));
                        bind
                    })
            })
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: CExpr<'e>) -> CExpr<'e> {
        let mut env = FunctionEnvs::new();

        env.start_function(self);
        debug!("Interpreting: {}", expr);
        let new_expr = self.compile(&mut SameLifetime::new(self.allocator), expr, &mut env);
        if let Some(new_expr) = new_expr {
            debug!("Interpreted to: {}", new_expr);
        }
        env.end_function(self);
        new_expr.unwrap_or(expr)
    }

    fn load_identifier(
        &mut self,
        _resolver: &dyn Resolver<'_, '_>,
        id: &Symbol,
    ) -> Option<CostBinding<'e>> {
        debug!("Find `{:?}`", id);
        self.find(id).map(|bind| {
            debug!("Loading `{}` at `{}` as `{}`", id, bind.cost, bind.bind);
            bind
        })
    }

    fn walk_expr<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        expr: CExpr<'b>,
        functions: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        match resolver.wrap(expr) {
            Reduced::Local(expr) => {
                struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
                    compiler: &'f mut Compiler<'a, 'e>,
                    functions: &'f mut FunctionEnvs<'e, 'a>,
                }
                impl<'a, 'e, 'f> Visitor<'e, 'e> for ReplaceVisitor<'a, 'e, 'f> {
                    type Producer = SameLifetime<'e>;

                    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                        self.compiler.compile(
                            &mut SameLifetime::new(self.compiler.allocator),
                            expr,
                            self.functions,
                        )
                    }
                    fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                        Some(self.compiler.allocator)
                    }
                }

                let mut visitor = ReplaceVisitor {
                    compiler: self,
                    functions,
                };
                walk_expr_alloc(&mut visitor, expr)
            }
            Reduced::Global(global) => {
                struct ReplaceVisitor<'a, 'e, 'f, 'r> {
                    compiler: &'f mut Compiler<'a, 'e>,
                    functions: &'f mut FunctionEnvs<'e, 'a>,
                    resolver: &'f dyn Resolver<'e, 'r>,
                    into_local: IntoLocal<'e, 'f>,
                }
                impl<'a, 'e, 'f, 'r> Visitor<'e, 'r> for ReplaceVisitor<'a, 'e, 'f, 'r> {
                    type Producer = IntoLocal<'e, 'f>;

                    fn visit_expr(&mut self, expr: CExpr<'r>) -> Option<CExpr<'e>> {
                        self.compiler.compile(self.resolver, expr, self.functions)
                    }
                    fn producer(&self) -> Self::Producer {
                        self.into_local.clone()
                    }

                    fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                        Some(self.compiler.allocator)
                    }
                }

                let info = &global.info;
                let allocator = self.allocator;
                let inlined_global_bindings = self.inlined_global_bindings;
                global.value.with(|make_expr, make_closure, expr| {
                    let different = Different {
                        allocator,
                        info,
                        inlined_global_bindings,
                        make_expr,
                        make_closure,
                    };

                    let mut visitor = ReplaceVisitor {
                        compiler: self,
                        functions,
                        resolver: &different,
                        into_local: IntoLocal {
                            allocator,
                            info,
                            inlined_global_bindings,
                            _marker: PhantomData,
                        },
                    };
                    walk_expr_alloc(&mut visitor, expr)
                })
            }
        }
    }

    fn update_identifiers<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        expr: CExpr<'b>,
        _functions: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        match resolver.wrap(expr) {
            Reduced::Local(expr) => {
                struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
                    compiler: &'f mut Compiler<'a, 'e>,
                }
                impl<'a, 'e, 'f> Visitor<'e, 'e> for ReplaceVisitor<'a, 'e, 'f> {
                    type Producer = SameLifetime<'e>;

                    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                        match expr {
                            Expr::Ident(id, _pos) => {
                                self.compiler
                                    .find(&id.name)
                                    .and_then(|bind| match bind.bind {
                                        Binding::Expr(expr)
                                            if bind.cost == 0
                                                && !self
                                                    .compiler
                                                    .contains_unbound_variables(expr.as_ref()) =>
                                        {
                                            Some(expr.into_local(
                                                &self.compiler.inlined_global_bindings,
                                                &self.compiler.allocator,
                                            ))
                                        }
                                        _ => None,
                                    })
                            }
                            _ => walk_expr_alloc(self, expr),
                        }
                    }
                    fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                        Some(self.compiler.allocator)
                    }
                }

                let mut visitor = ReplaceVisitor { compiler: self };
                visitor.visit_expr(expr)
            }
            Reduced::Global(global) => {
                struct ReplaceVisitor<'a, 'e, 'f> {
                    compiler: &'f mut Compiler<'a, 'e>,
                    into_local: IntoLocal<'e, 'f>,
                }
                impl<'a, 'e, 'f, 'r> Visitor<'e, 'r> for ReplaceVisitor<'a, 'e, 'f> {
                    type Producer = IntoLocal<'e, 'f>;

                    fn visit_expr(&mut self, expr: CExpr<'r>) -> Option<CExpr<'e>> {
                        match expr {
                            Expr::Ident(id, _) => {
                                self.compiler
                                    .find(&id.name)
                                    .and_then(|bind| match bind.bind {
                                        Binding::Expr(expr) if bind.cost == 0 => {
                                            Some(expr.into_local(
                                                &self.compiler.inlined_global_bindings,
                                                &self.compiler.allocator,
                                            ))
                                        }
                                        _ => None,
                                    })
                            }
                            _ => walk_expr_alloc(self, expr),
                        }
                    }
                    fn producer(&self) -> Self::Producer {
                        self.into_local.clone()
                    }

                    fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                        Some(self.compiler.allocator)
                    }
                }

                let info = &global.info;
                let allocator = self.allocator;
                let inlined_global_bindings = self.inlined_global_bindings;
                global.value.with(|_make_expr, _make_closure, expr| {
                    let mut visitor = ReplaceVisitor {
                        compiler: self,
                        into_local: IntoLocal {
                            allocator,
                            info,
                            inlined_global_bindings,
                            _marker: PhantomData,
                        },
                    };
                    visitor.visit_expr(expr)
                })
            }
        }
    }

    #[allow(dead_code)]
    fn update_types(
        &mut self,
        map: &mut FnvMap<Symbol, ArcType>,
        expr: CExpr<'e>,
    ) -> Option<CExpr<'e>> {
        struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
            compiler: &'f mut Compiler<'a, 'e>,
            map: &'f mut FnvMap<Symbol, ArcType>,
        }
        impl<'a, 'e, 'f> Visitor<'e, 'e> for ReplaceVisitor<'a, 'e, 'f> {
            type Producer = SameLifetime<'e>;

            fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                walk_expr_alloc(self, expr)
            }

            fn visit_type(&mut self, typ: &'e ArcType) -> Option<ArcType> {
                typ.replace_generics(&mut base::types::NullInterner, &mut self.map)
            }

            fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                Some(self.compiler.allocator)
            }
        }

        let mut visitor = ReplaceVisitor {
            compiler: self,
            map,
        };
        visitor.visit_expr(expr)
    }

    fn compile<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        mut expr: CExpr<'b>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        let mut tail = self.compile_(resolver, expr, function);
        let mut bindings = Vec::new();
        loop {
            expr = match tail {
                TailCall::Tail(original, tail, expr) => {
                    bindings.push((original, tail));
                    expr
                }
                TailCall::Value(mut value) => {
                    let allocator = self.allocator;
                    let optimized = self.optimize_top(
                        value
                            .map(Reduced::Local)
                            .unwrap_or_else(|| resolver.wrap(expr)),
                        function,
                    );
                    if let Some(opt_expr) = optimized {
                        if !ptr::eq::<Expr>(opt_expr, expr) {
                            value = optimized;
                        }
                    }

                    return bindings.into_iter().rev().fold(
                        value,
                        |mut value, (original, tail)| {
                            let optimized = self.optimize_top(
                                value
                                    .map(Reduced::Local)
                                    .unwrap_or_else(|| resolver.wrap(original)),
                                function,
                            );
                            if let Some(opt_expr) = optimized {
                                if !ptr::eq::<Expr>(opt_expr, expr) {
                                    value = optimized;
                                }
                            }
                            self.stack_constructors.exit_scope();
                            self.bindings_in_scope.exit_scope();
                            self.local_bindings.exit_scope();

                            match tail {
                                Tail::Match {
                                    scrutinee_expr,
                                    new_expr,
                                    alt,
                                } => {
                                    let new_alt = value.map(|expr| {
                                        &*allocator.alternative_arena.alloc(Alternative {
                                            pattern: alt.pattern.clone(),
                                            expr,
                                        })
                                    });
                                    optimize::merge_match_fn(
                                        allocator,
                                        scrutinee_expr,
                                        |expr| resolver.produce(expr),
                                        new_expr,
                                        slice::from_ref(alt),
                                        |alt| resolver.produce_alts(&alt),
                                        new_alt.map(slice::from_ref),
                                    )
                                }
                                Tail::Let {
                                    bind,
                                    new_bind,
                                    body,
                                } => merge_fn(
                                    &bind,
                                    |b| {
                                        &*self.allocator.let_binding_arena.alloc(LetBinding {
                                            expr: match &b.expr {
                                                Named::Expr(expr) => {
                                                    Named::Expr(resolver.produce(expr))
                                                }
                                                Named::Recursive(closures) => Named::Recursive(
                                                    closures
                                                        .iter()
                                                        .map(|closure| Closure {
                                                            pos: closure.pos,
                                                            name: closure.name.clone(),
                                                            args: closure.args.clone(),
                                                            expr: resolver.produce(closure.expr),
                                                        })
                                                        .collect(),
                                                ),
                                            },
                                            name: b.name.clone(),
                                            span_start: b.span_start,
                                        })
                                    },
                                    new_bind,
                                    &body,
                                    |body| resolver.produce(body),
                                    value,
                                    |bind, body| match &bind.expr {
                                        Named::Recursive(closures) if closures.is_empty() => body,
                                        _ => &*allocator.arena.alloc(Expr::Let(bind, body)),
                                    },
                                ),
                            }
                        },
                    );
                }
            };

            tail = self.compile_(resolver, expr, function);
        }
    }

    fn compile_<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        expr: CExpr<'b>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> TailCall<'e, 'b, Option<CExpr<'e>>> {
        let reduced = match *expr {
            Expr::Const(_, _) | Expr::Ident(..) => None,
            Expr::Let(ref let_binding, ref body) => {
                self.stack_constructors.enter_scope();
                self.bindings_in_scope.enter_scope();
                self.local_bindings.enter_scope();
                let new_named = match let_binding.expr {
                    core::Named::Expr(ref bind_expr) => {
                        trace!("Optimizing {}", let_binding.name.name);
                        let reduced = self.compile(resolver, bind_expr, function);

                        let name = if let Some(reduced) = &reduced {
                            trace!("Optimized to {}", reduced);
                            self.rename(&let_binding.name, let_binding.bind_span())
                        } else {
                            let_binding.name.name.clone()
                        };
                        self.push_stack_var(
                            resolver,
                            name,
                            Some(
                                reduced
                                    .map(Reduced::Local)
                                    .unwrap_or_else(|| resolver.wrap(bind_expr))
                                    .into(),
                            ),
                        );
                        reduced.map(Named::Expr)
                    }
                    core::Named::Recursive(ref closures) => {
                        for closure in closures.iter() {
                            trace!(
                                "Optimizing {} from \\{} -> {}",
                                closure.name.name,
                                closure.args.iter().map(|id| &id.name).format(" "),
                                closure.expr
                            );
                            let name =
                                self.rename(&closure.name, Span::new(closure.pos, closure.pos));
                            let closure_bind = resolver.wrap_closure(ClosureRef {
                                id: &closure.name,
                                args: &closure.args[..],
                                body: closure.expr,
                            });
                            self.push_stack_var(resolver, name, Some(closure_bind.into()));
                        }
                        let new_closures = merge_collect(
                            self,
                            closures,
                            |self_, closure| {
                                let new_body =
                                    self_.compile_lambda(resolver, closure.as_ref(), function);
                                new_body.map(|body| {
                                    trace!(
                                        "Optimized {} to \\{} -> {}",
                                        closure.name.name,
                                        closure.args.iter().map(|id| &id.name).format(" "),
                                        body
                                    );
                                    let name = self_.get_rename(&closure.name.name);
                                    self_.bindings_in_scope.insert(name.clone(), ());

                                    Closure {
                                        pos: closure.pos,
                                        name: TypedIdent {
                                            name,
                                            typ: closure.name.typ.clone(),
                                        },
                                        args: closure.args.clone(),
                                        expr: body,
                                    }
                                })
                            },
                            |self_, closure| Closure {
                                pos: closure.pos,
                                name: TypedIdent {
                                    name: self_.get_rename(&closure.name.name),
                                    typ: closure.name.typ.clone(),
                                },
                                args: closure.args.clone(),
                                expr: resolver.produce(closure.expr),
                            },
                        )
                        .map(Named::Recursive);

                        if new_closures.is_none() {
                            for closure in closures {
                                self.remove_rename(&closure.name.name);
                            }
                        }

                        new_closures
                    }
                };

                return TailCall::Tail(
                    expr,
                    Tail::Let {
                        new_bind: new_named.map(|expr| {
                            let name = match &let_binding.expr {
                                Named::Expr(_) => self.get_rename(&let_binding.name.name),
                                Named::Recursive(_) => let_binding.name.name.clone(),
                            };

                            let let_binding =
                                &*self.allocator.let_binding_arena.alloc(LetBinding {
                                    expr,
                                    name: TypedIdent {
                                        name,
                                        typ: let_binding.name.typ.clone(),
                                    },
                                    span_start: let_binding.span_start,
                                });

                            if let Named::Recursive(closures) = &let_binding.expr {
                                for closure in closures {
                                    self.push_stack_var(
                                        resolver,
                                        closure.name.name.clone(),
                                        Some(Reduced::Local(closure.as_ref()).into()),
                                    );
                                }
                            }

                            let_binding
                        }),
                        bind: let_binding,
                        body,
                    },
                    body,
                );
            }

            Expr::Match(scrutinee_expr, alts) if alts.len() == 1 => {
                let new_expr = self.compile(resolver, scrutinee_expr, function);
                self.stack_constructors.enter_scope();
                self.bindings_in_scope.enter_scope();
                self.local_bindings.enter_scope();

                let alt = &alts[0];
                match alt.pattern {
                    Pattern::Constructor(_, ref args) => {
                        for arg in args.iter() {
                            self.push_unknown_stack_var(arg.name.clone());
                        }
                    }
                    Pattern::Record { .. } => {
                        let scrutinee_expr = self.peek_reduced_expr(resolver.wrap(scrutinee_expr));
                        self.compile_let_pattern(resolver, &alt.pattern, scrutinee_expr, function);
                    }
                    Pattern::Ident(ref id) => {
                        let bind = self.peek_reduced(resolver.wrap(scrutinee_expr)).bind;
                        self.push_stack_var(resolver, id.name.clone(), Some(bind));
                    }
                    Pattern::Literal(_) => (),
                }

                return TailCall::Tail(
                    expr,
                    Tail::Match {
                        scrutinee_expr,
                        new_expr,
                        alt,
                    },
                    &alt.expr,
                );
            }

            Expr::Match(expr, alts) => {
                let allocator = self.allocator;
                let new_expr = self.compile(resolver, expr, function);
                let new_alts = optimize::merge_slice_produce2(
                    Some(allocator),
                    alts,
                    |alt| Alternative {
                        pattern: alt.pattern.clone(),
                        expr: resolver.produce(alt.expr),
                    },
                    |alt| {
                        self.stack_constructors.enter_scope();
                        self.bindings_in_scope.enter_scope();
                        self.local_bindings.enter_scope();

                        match alt.pattern {
                            Pattern::Constructor(_, ref args) => {
                                for arg in args.iter() {
                                    self.push_unknown_stack_var(arg.name.clone());
                                }
                            }
                            Pattern::Record { .. } => {
                                let expr = self.peek_reduced_expr(resolver.wrap(expr));
                                self.compile_let_pattern(resolver, &alt.pattern, expr, function);
                            }
                            Pattern::Ident(ref id) => {
                                let bind = self.peek_reduced(resolver.wrap(expr)).bind;
                                self.push_stack_var(resolver, id.name.clone(), Some(bind));
                            }
                            Pattern::Literal(_) => (),
                        }

                        let new_expr = self.compile(resolver, &alt.expr, function);

                        self.bindings_in_scope.exit_scope();
                        self.stack_constructors.exit_scope();
                        self.local_bindings.exit_scope();

                        new_expr.map(|expr| Alternative {
                            pattern: alt.pattern.clone(),
                            expr,
                        })
                    },
                );

                if new_expr.is_some() || new_alts.is_some() {
                    optimize::merge_match_fn(
                        allocator,
                        expr,
                        |expr| resolver.produce(expr),
                        new_expr,
                        alts,
                        |alts| resolver.produce_alts(alts),
                        new_alts,
                    )
                } else {
                    None
                }
            }
            Expr::Call(..) | Expr::Data(..) | Expr::Cast(..) => {
                self.walk_expr(resolver, expr, function)
            }
        };
        TailCall::Value(reduced)
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
                            trace!("Unbound {:?}", id.name);
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
        mut expr: ReducedExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        let mut replaced_expr = Vec::new();
        for i in 0..10 {
            trace!("Optimizing {}: {}", i, expr);
            let replaced_expr_len = replaced_expr.len();
            let new_expr = self
                .peek_reduced_expr_fn(expr.clone(), &mut |cost, e| {
                    replaced_expr.push((cost, e.clone()))
                })
                .with(
                    self.allocator,
                    self.inlined_global_bindings,
                    |resolver, reduced_expr| -> Option<_> {
                        match reduced_expr {
                            Expr::Call(..) => {
                                let (f, args) = split_call(reduced_expr);
                                self.inline_call(function, resolver, reduced_expr, f, args)
                                    .map(Reduced::Local)
                            }
                            Expr::Ident(..) => self
                                .inline_call(
                                    function,
                                    resolver,
                                    reduced_expr,
                                    reduced_expr,
                                    [].iter(),
                                )
                                .map(Reduced::Local)
                                .or_else(|| {
                                    if !ptr::eq::<Expr>(expr.as_ref(), reduced_expr) {
                                        Some(resolver.wrap(reduced_expr))
                                    } else {
                                        None
                                    }
                                }),
                            Expr::Const(..) if !ptr::eq::<Expr>(expr.as_ref(), reduced_expr) => {
                                Some(resolver.wrap(reduced_expr))
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

                    break;
                }
                Some(e) => {
                    expr = e.clone();
                    replaced_expr.push((0, e));
                }
            }
        }

        let (_, e) = replaced_expr.into_iter().rev().find(|(cost, e)| {
            if *cost <= 10 && !self.contains_unbound_variables(e.as_ref()) {
                trace!("Optimized to {}: {}", cost, e);
                true
            } else {
                trace!("Unable to optimize {}: {}", cost, e);
                false
            }
        })?;

        // Go through the inner expression so that any bound patterns are updated
        let e = e
            .clone()
            .with(
                self.allocator,
                self.inlined_global_bindings,
                |resolver, e| self.update_identifiers(resolver, e, function),
            )
            .unwrap_or_else(|| e.into_local(&self.inlined_global_bindings, &self.allocator));
        Some(e)
    }

    fn inline_call<'b>(
        &mut self,
        _function: &mut FunctionEnvs<'e, 'a>,
        resolver: &dyn Resolver<'e, 'b>,
        expr: CExpr<'b>,
        f: CExpr<'b>,
        mut args: impl ExactSizeIterator<Item = &'b Expr<'b>> + Clone,
    ) -> Option<CExpr<'e>> {
        let f2 = self.peek_reduced(resolver.wrap(f));
        trace!("TRY INLINE {} ## {}", expr, f2.bind);
        match f2.bind {
            Binding::Expr(peek_f) => match peek_f.as_ref() {
                Expr::Ident(ref id, ..) => {
                    if id.name.is_primitive() && args.len() == 2 {
                        let l = resolver.wrap(args.next().unwrap());
                        let r = resolver.wrap(args.next().unwrap());
                        self.reduce_primitive_binop(expr, id, l, r)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Binding::Closure(..) => None,
        }
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
        for _ in 0..10 {
            let new_bind = expr.clone().with(
                self.allocator,
                self.inlined_global_bindings,
                |resolver, expr| match peek_through_lets(expr) {
                    Expr::Ident(ref id, _) => {
                        self.load_identifier(resolver, &id.name).or_else(|| {
                            resolver.find(&id.name).map(|bind| match bind {
                                Binding::Expr(e) => CostBinding {
                                    cost: 1,
                                    bind: Binding::Expr(Reduced::Global(e)),
                                },
                                Binding::Closure(c) => CostBinding {
                                    cost: 1,
                                    bind: Binding::Closure(Reduced::Global(c)),
                                },
                            })
                        })
                    }
                    Expr::Match(match_expr, alts) => {
                        let match_expr = self.peek_reduced_expr(resolver.wrap(match_expr));

                        // Constant fold field projection
                        if alts.len() == 1 {
                            let alt = &alts[0];
                            match (&alt.pattern, &alt.expr) {
                                (Pattern::Record { fields, .. }, Expr::Ident(id, _))
                                    if fields.len() == 1
                                        && id.name
                                            == *fields[0]
                                                .1
                                                .as_ref()
                                                .unwrap_or(&fields[0].0.name) =>
                                {
                                    let field = &fields[0];
                                    let projected =
                                        self.project_reduced(&field.0.name, match_expr.clone())?;
                                    return Some(CostBinding {
                                        cost: 1,
                                        bind: Binding::Expr(projected),
                                    });
                                }
                                (Pattern::Record { .. }, _) | (Pattern::Ident(_), _) => {
                                    return Some(CostBinding {
                                        cost: 1,
                                        bind: Binding::Expr(resolver.wrap(alt.expr)),
                                    })
                                }
                                _ => (),
                            }
                        }
                        // Constant fold pattern matches
                        match_expr.with(
                            self.allocator,
                            self.inlined_global_bindings,
                            |match_resolver, match_expr| match match_expr {
                                Expr::Data(id, data_args, ..) => alts
                                    .iter()
                                    .find(|alt| match &alt.pattern {
                                        Pattern::Constructor(ctor_id, args) => {
                                            if ctor_id.name.name_eq(&id.name) {
                                                debug_assert!(data_args.len() == args.len());
                                                for (data, arg) in data_args.iter().zip(args) {
                                                    self.push_inline_stack_var(
                                                        arg.name.clone(),
                                                        Some(match_resolver.wrap(data).into()),
                                                    );
                                                }
                                                true
                                            } else {
                                                false
                                            }
                                        }
                                        Pattern::Ident(_) => true,
                                        _ => false,
                                    })
                                    .map(|alt| CostBinding {
                                        cost: 1,
                                        bind: Binding::Expr(resolver.wrap(alt.expr)),
                                    }),
                                _ => None,
                            },
                        )
                    }
                    peek if !ptr::eq::<Expr>(peek, expr) => Some(CostBinding {
                        cost: 1,
                        bind: Binding::Expr(resolver.wrap(peek)),
                    }),
                    _ => None,
                },
            );

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
                        cost: 1,
                        bind: Binding::Expr(expr),
                    }
                }
            }
        }
        CostBinding {
            cost: 1,
            bind: Binding::Expr(expr),
        }
    }

    fn project_reduced(
        &mut self,
        symbol: &Symbol,
        expr: ReducedExpr<'e>,
    ) -> Option<ReducedExpr<'e>> {
        trace!("Project {} . {}", expr, symbol);
        match self
            .peek_identifier(expr.clone())
            .map(|b| b.bind)
            .unwrap_or(Binding::Expr(expr.clone()))
        {
            Binding::Expr(expr) => expr.with(
                self.allocator,
                self.inlined_global_bindings,
                |resolver, expr| match expr {
                    Expr::Data(id, fields, ..) => {
                        let (_, projected_expr) = id
                            .typ
                            .row_iter()
                            .zip(*fields)
                            .find(|(field, _)| field.name.declared_name() == symbol.declared_name())
                            .unwrap_or_else(|| {
                                ice!("Missing record field {} in {}", symbol, id.typ)
                            });
                        trace!("Projected: {}", projected_expr);
                        Some(resolver.wrap(projected_expr))
                    }
                    _ => None,
                },
            ),
            _ => None,
        }
    }

    fn peek_identifier(&mut self, expr: ReducedExpr<'e>) -> Option<CostBinding<'e>> {
        expr.with(
            self.allocator,
            self.inlined_global_bindings,
            |resolver, expr| {
                match peek_through_lets(expr) {
                    Expr::Ident(id, ..) => Some(match self.load_identifier(resolver, &id.name) {
                        Some(bind) => bind,
                        None => match resolver.find(&id.name) {
                            // TODO Forward cost from find
                            Some(Binding::Expr(expr)) => CostBinding {
                                cost: 1,
                                bind: Binding::Expr(Reduced::Global(expr)),
                            },
                            Some(Binding::Closure(c)) => CostBinding {
                                cost: 1,
                                bind: Binding::Closure(Reduced::Global(c)),
                            },
                            None => return None,
                        },
                    }),
                    new_expr if !ptr::eq::<Expr>(expr, new_expr) => Some(CostBinding {
                        cost: 1,
                        bind: Binding::Expr(resolver.wrap(new_expr)),
                    }),
                    _ => None,
                }
            },
        )
    }

    fn compile_let_pattern(
        &mut self,
        resolver: &dyn Resolver<'e, '_>,
        pattern: &Pattern,
        pattern_expr: ReducedExpr<'e>,
        _function: &mut FunctionEnvs<'e, 'a>,
    ) {
        let pattern_expr = self.peek_reduced_expr(pattern_expr);
        trace!("### {}", pattern_expr);
        match pattern {
            Pattern::Ident(name) => {
                self.push_stack_var(resolver, name.name.clone(), Some(pattern_expr.into()));
            }
            Pattern::Record { fields, .. } => pattern_expr.with(
                self.allocator,
                self.inlined_global_bindings,
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
                            self.push_stack_var(resolver, field_name, expr);
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

    fn compile_lambda<'b>(
        &mut self,
        resolver: &dyn Resolver<'e, 'b>,
        closure: ClosureRef<'b>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<CExpr<'e>> {
        debug!(
            "Lambda {} {}",
            closure.id.name,
            closure.args.iter().map(|id| &id.name).format(" ")
        );
        function.start_function(self);

        self.bindings_in_scope.enter_scope();
        self.local_bindings.enter_scope();

        for arg in closure.args {
            self.push_unknown_stack_var(arg.name.clone());
        }
        let body = self.compile(resolver, closure.body, function);

        self.bindings_in_scope.exit_scope();
        self.local_bindings.exit_scope();

        function.end_function(self);
        body
    }

    fn reduce_primitive_binop<'b>(
        &mut self,
        expr: CExpr<'b>,
        id: &TypedIdent<Symbol>,
        l: ReducedExpr<'e>,
        r: ReducedExpr<'e>,
    ) -> Option<CExpr<'e>> {
        use std::ops::{Add, Div, Mul, Sub};

        fn binop<T>(name: &Symbol, l: T, r: T) -> Option<T>
        where
            T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
        {
            Some(match name.as_ref().chars().last().unwrap() {
                '+' => l + r,
                '-' => l - r,
                '*' => l * r,
                '/' => l / r,
                _ => return None,
            })
        }

        trace!("Fold binop {} {} {}", l, id.name, r);
        let l = self.peek_reduced_expr(l);
        let r = self.peek_reduced_expr(r);
        let output = match (l.as_ref(), r.as_ref()) {
            (&Expr::Const(Literal::Int(l), ..), &Expr::Const(Literal::Int(r), ..)) => {
                Literal::Int(binop(&id.name, l, r)?)
            }
            (&Expr::Const(Literal::Float(l), ..), &Expr::Const(Literal::Float(r), ..)) => {
                Literal::Float(binop(&id.name, l, r)?)
            }
            _ => return None,
        };
        Some(self.allocator.arena.alloc(Expr::Const(output, expr.span())))
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
        source,
        symbol::Symbols,
    };

    use crate::core::grammar::ExprParser;
    use crate::core::*;

    use crate::core::tests::PatternEq;

    fn from_lalrpop<T, U>(
        err: lalrpop_util::ParseError<usize, T, U>,
    ) -> Spanned<Box<dyn ::std::error::Error + Send + Sync>, BytePos>
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
                let mut source = source::CodeMap::new();
                source.add_filemap("test".into(), expr_str.into());

                let mut errors = Errors::new();
                errors.push(from_lalrpop(err));

                panic!("{}", base::error::InFile::new(source, errors))
            });

        allocator.arena.alloc(actual_expr)
    }

    fn compile_and_optimize(
        globals: &dyn Fn(&Symbol) -> Option<GlobalBinding>,
        actual: &str,
    ) -> Global<CoreExpr> {
        let mut symbols = Symbols::new();

        let allocator = Arc::new(Allocator::new());

        let actual_expr = parse_expr(&mut symbols, &allocator, actual);

        let mut dep_graph = crate::core::dead_code::DepGraph::default();
        let used_bindings = dep_graph.used_bindings(actual_expr);

        let pure_symbols = crate::core::purity::purity(actual_expr);

        let actual_expr =
            crate::core::dead_code::dead_code_elimination(&used_bindings, &allocator, actual_expr);

        let cyclic_bindings: FnvSet<_> = dep_graph.cycles().flat_map(|cycle| cycle).collect();

        let costs = crate::core::costs::analyze_costs(&cyclic_bindings, actual_expr);

        let env = base::ast::EmptyEnv::default();
        let inlined_global_bindings = Default::default();
        let mut interpreter = Compiler::new(&allocator, globals, &env, &inlined_global_bindings)
            .costs(costs)
            .cyclic_bindings(cyclic_bindings)
            .pure_symbols(&pure_symbols);
        let actual_expr = interpreter.compile_expr(actual_expr);

        let mut dep_graph = crate::core::dead_code::DepGraph::default();
        let used_bindings = dep_graph.used_bindings(actual_expr);
        let expr =
            crate::core::dead_code::dead_code_elimination(&used_bindings, &allocator, actual_expr);
        Global {
            value: crate::core::freeze_expr(&allocator, expr),
            info: Arc::new(interpreter.optimizer_info(&allocator)),
        }
    }

    macro_rules! assert_eq_expr {
        ($actual:expr, $expected:expr) => {
            assert_eq_expr!($actual, $expected, |_: &Symbol| None)
        };
        ($actual:expr, $expected:expr, $globals:expr) => {{
            let mut symbols = Symbols::new();
            let allocator = Allocator::new();
            let actual = compile_and_optimize(&$globals, $actual);

            let expected_expr = parse_expr(&mut symbols, &allocator, $expected);

            assert_deq!(PatternEq(actual.value.expr()), *expected_expr);
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
        assert_eq_expr!(expr, "1", move |_: &_| Some(Binding::from(Global {
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

    #[ignore]
    #[test]
    fn fold_function_call_basic() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x y = (#Int+) x y
            in f 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[ignore]
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

    #[ignore]
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

    #[ignore]
    #[test]
    fn fold_function_call_partial() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let f x = (rec let f2 y = (#Int+) x y in f2) in
            let g = f 10 in
            (#Int+) (f 1 2) (g 3)
        "#;
        assert_eq_expr!(expr, "16");
    }

    #[ignore]
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

    #[ignore]
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

    #[ignore]
    #[test]
    fn factorial() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            rec let lt l r = (#Int<) l r
            in
            rec let mul l r = (#Int*) l r
            in
            rec let sub l r = (#Int-) l r
            in

            rec let factorial n =
                match lt n 2 with
                | True -> 1
                | False -> mul n (factorial (sub n 1))
                end
            in
            factorial
        "#;
        let expected = r#"
        rec let factorial n =
            match (#Int<) n 2 with
            | True -> 1
            | False -> (#Int*) n (factorial ( (#Int-) n 1))
            end
        in
        factorial
        "#;
        assert_eq_expr!(expr, expected);
    }

    #[ignore]
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

    fn global_func(symbols: &mut Symbols) -> Global<CoreExpr> {
        let mut pure_symbols = None;
        let mut costs = Default::default();

        let global = with_allocator(|global_allocator| {
            let expr = ExprParser::new()
                .parse(
                    symbols,
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

        let info = Arc::new(OptimizerInfo {
            local_bindings: vec![(
                symbols.simple_symbol("f"),
                global
                    .clone()
                    .with(|_, make_closure, global| match *global {
                        Expr::Let(ref bind, _) => match bind.expr {
                            Named::Recursive(ref closures) => {
                                Binding::from(make_closure(closures[0].as_ref()))
                            }
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
        Global {
            info,
            value: global,
        }
    }

    #[ignore]
    #[test]
    fn fold_global_function_call_with_unknown_parameters() {
        let _ = ::env_logger::try_init();
        let mut symbols = Symbols::new();
        let global = global_func(&mut symbols);

        let expr = r#"
            rec let g y = global.f 2 y in
            g
        "#;

        assert_eq_expr!(
            expr,
            r#"
                rec let g y = (#Int+) 2 y in
                g
            "#,
            |s: &Symbol| match s.as_ref() {
                "global" => Some(Binding::from(global.clone())),
                _ => None,
            }
        );
    }

    #[ignore]
    #[test]
    fn fold_global_function_call_through_two_modules_simple() {
        let _ = ::env_logger::try_init();
        let mut symbols = Symbols::new();
        let global = global_func(&mut symbols);

        let global2 = compile_and_optimize(
            &|s: &Symbol| match s.as_ref() {
                "global1" => Some(Binding::from(global.clone())),
                _ => None,
            },
            "let x = global1 in x",
        );

        let local_bindings = &global2.info.local_bindings;
        assert!(
            local_bindings.keys().any(|s| s.declared_name() == "x_inl")
                && local_bindings
                    .keys()
                    .any(|s| s.declared_name() == "global1"),
            "x and global should be in the local_bindings: {:#?}",
            global2.info.local_bindings.keys().collect::<Vec<_>>(),
        );
        assert_eq_expr!(
            r#"
                rec let g y = global2.f 2 y in
                g
            "#,
            r#"
                rec let g y = (#Int+) 2 y in
                g
            "#,
            |s: &Symbol| match s.as_ref() {
                "global2" => Some(Binding::from(global2.clone())),
                _ => None,
            }
        );
    }
}
