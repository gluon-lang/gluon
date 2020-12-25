#[macro_export]
#[cfg(any(test, feature = "test"))]
macro_rules! assert_deq {
    ($left:expr, $right:expr) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    difference::assert_diff!(
                        &left_val.to_string(),
                        &right_val.to_string(),
                        "\n",
                        0
                    );
                }
            }
        }
    }};
}

#[cfg(any(test, feature = "test"))]
lalrpop_util::lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    #[allow(unused_parens)]
    pub grammar,
    "/core/grammar.rs"
);
pub mod costs;
pub mod dead_code;
pub mod interpreter;
pub mod optimize;
#[cfg(feature = "test")]
mod pretty;
pub mod purity;

use std::{borrow::Cow, cell::RefCell, collections::HashMap, fmt, iter::once, mem, sync::Arc};

use {itertools::Itertools, ordered_float::NotNan, smallvec::SmallVec, typed_arena::Arena};

use self::optimize::{walk_expr_alloc, SameLifetime, Visitor};

use crate::base::{
    ast::{self, SpannedExpr, SpannedPattern, Typed, TypedIdent},
    fnv::{FnvMap, FnvSet},
    pos::{spanned, BytePos, Span, Spanned},
    resolve::remove_aliases_cow,
    symbol::Symbol,
    types::{arg_iter, ArcType, NullInterner, PrimitiveEnv, Type, TypeEnv, TypeExt},
};

macro_rules! iterator {
    ($($expr : expr),* $(,)?) => {
        [$(Some($expr)),*].iter_mut().map(|e| e.take().unwrap())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Closure<'a> {
    pub pos: BytePos,
    pub name: TypedIdent<Symbol>,
    pub args: Vec<TypedIdent<Symbol>>,
    pub expr: &'a Expr<'a>,
}

impl fmt::Display for Closure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            ClosureRef {
                id: &self.name,
                args: &self.args,
                body: self.expr
            }
        )
    }
}

impl<'a> Closure<'a> {
    pub fn as_ref(&'a self) -> ClosureRef<'a> {
        ClosureRef {
            id: &self.name,
            args: &self.args,
            body: &self.expr,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Named<'a> {
    Recursive(Vec<Closure<'a>>),
    Expr(&'a Expr<'a>),
}

impl fmt::Display for Named<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Recursive(cs) => {
                for c in cs {
                    writeln!(f, "{}", c)?;
                }
                Ok(())
            }
            Self::Expr(e) => write!(f, "{}", e),
        }
    }
}

impl<'a> Default for Named<'a> {
    fn default() -> Self {
        Named::Recursive(Vec::new())
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct LetBinding<'a> {
    pub name: TypedIdent<Symbol>,
    pub expr: Named<'a>,
    pub span_start: BytePos,
}

impl LetBinding<'_> {
    pub fn bind_span(&self) -> Span<BytePos> {
        Span::new(
            self.span_start,
            self.span_start
                + codespan::ByteOffset::from(self.name.name.declared_name().len() as i64),
        )
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Literal {
    Byte(u8),
    Int(i64),
    Float(NotNan<f64>),
    String(Box<str>),
    Char(char),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Constructor(TypedIdent<Symbol>, Vec<TypedIdent<Symbol>>),
    Record {
        typ: ArcType,
        fields: Vec<(TypedIdent<Symbol>, Option<Symbol>)>,
    },
    Ident(TypedIdent<Symbol>),
    Literal(Literal),
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Alternative<'a> {
    pub pattern: Pattern,
    pub expr: &'a Expr<'a>,
}

pub type CExpr<'a> = &'a Expr<'a>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Const(Literal, Span<BytePos>),
    Ident(TypedIdent<Symbol>, Span<BytePos>),
    Call(CExpr<'a>, &'a [Expr<'a>]),
    Data(TypedIdent<Symbol>, &'a [Expr<'a>], BytePos),
    Let(&'a LetBinding<'a>, CExpr<'a>),
    Match(CExpr<'a>, &'a [Alternative<'a>]),
    Cast(CExpr<'a>, ArcType),
}

#[cfg(feature = "test")]
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = ::pretty::Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena).1.render(100, &mut s).unwrap();
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}
#[cfg(not(feature = "test"))]
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(feature = "test")]
impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use crate::core::pretty::Prec;
        let arena = ::pretty::Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena, Prec::Top)
            .1
            .render(100, &mut s)
            .unwrap();
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

#[cfg(not(feature = "test"))]
impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Default for &'static Expr<'static> {
    fn default() -> Self {
        static X: Expr<'static> =
            Expr::Const(Literal::Int(0), Span::new_unchecked(BytePos(0), BytePos(0)));
        &X
    }
}

impl<'a> Default for Expr<'a> {
    fn default() -> Self {
        Expr::Const(Literal::default(), Span::default())
    }
}

impl Default for Pattern {
    fn default() -> Self {
        Pattern::Literal(Literal::default())
    }
}

impl Literal {
    fn from_ast(literal: &ast::Literal) -> Self {
        match literal {
            ast::Literal::Byte(x) => Literal::Byte(*x),
            ast::Literal::Int(x) => Literal::Int(*x),
            ast::Literal::Float(x) => Literal::Float(*x),
            ast::Literal::String(x) => Literal::String(Box::from(&x[..])),
            ast::Literal::Char(x) => Literal::Char(*x),
        }
    }
}

impl Default for Literal {
    fn default() -> Self {
        Literal::Int(0)
    }
}

impl Typed for Literal {
    type Ident = Symbol;

    fn try_type_of(&self, _: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType, String> {
        Ok(match *self {
            Literal::Int(_) => Type::int(),
            Literal::Float(_) => Type::float(),
            Literal::Byte(_) => Type::byte(),
            Literal::String(_) => Type::string(),
            Literal::Char(_) => Type::char(),
        })
    }
}

#[derive(Default)]
#[must_use]
struct Binder<'a> {
    bindings: Vec<LetBinding<'a>>,
}

impl<'a> Binder<'a> {
    fn bind(&mut self, expr: CExpr<'a>, typ: ArcType) -> Expr<'a> {
        let name = TypedIdent {
            name: Symbol::from(format!("bind_arg{:p}", expr)),
            typ,
        };
        self.bind_id(name, expr)
    }

    fn bind_id(&mut self, name: TypedIdent<Symbol>, expr: CExpr<'a>) -> Expr<'a> {
        let ident_expr = Expr::Ident(name.clone(), expr.span());
        self.bindings.push(LetBinding {
            name,
            expr: Named::Expr(expr),
            span_start: ident_expr.span().start(),
        });
        ident_expr
    }

    fn into_expr(self, allocator: &'a Allocator<'a>, expr: Expr<'a>) -> Expr<'a> {
        self.bindings.into_iter().rev().fold(expr, |expr, bind| {
            Expr::Let(
                allocator.let_binding_arena.alloc(bind),
                allocator.arena.alloc(expr),
            )
        })
    }

    fn into_expr_ref(self, allocator: &'a Allocator<'a>, expr: &'a Expr<'a>) -> &'a Expr<'a> {
        self.bindings.into_iter().rev().fold(expr, |expr, bind| {
            allocator
                .arena
                .alloc(Expr::Let(allocator.let_binding_arena.alloc(bind), expr))
        })
    }
}

impl<'a> Expr<'a> {
    pub fn span(&self) -> Span<BytePos> {
        match *self {
            Expr::Call(expr, args) => {
                let span = expr.span();
                Span::new(span.start(), args.last().unwrap().span().end())
            }
            Expr::Const(_, span) => span,
            Expr::Data(_, args, span_start) => {
                let span_end = args.last().map_or(span_start, |arg| arg.span().end());
                Span::new(span_start, span_end)
            }
            Expr::Ident(_, span) => span,
            Expr::Let(ref let_binding, ref body) => {
                let span_end = body.span();
                Span::new(let_binding.span_start, span_end.end())
            }
            Expr::Match(expr, alts) => {
                let span_start = expr.span();
                Span::new(span_start.start(), alts.last().unwrap().expr.span().end())
            }

            Expr::Cast(expr, ..) => expr.span(),
        }
    }
}

fn is_constructor(s: &Symbol) -> bool {
    s.as_str()
        .rsplit('.')
        .next()
        .unwrap()
        .starts_with(char::is_uppercase)
}

#[derive(Clone, Debug)]
pub struct ClosureRef<'a> {
    pub id: &'a TypedIdent<Symbol>,
    pub args: &'a [TypedIdent<Symbol>],
    pub body: CExpr<'a>,
}

impl fmt::Display for ClosureRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "let {} {} = {}",
            self.id.name,
            self.args.iter().map(|arg| &arg.name).format(" "),
            self.body
        )
    }
}

mod internal {
    use super::*;

    use std::{
        hash::{Hash, Hasher},
        ptr,
        sync::Arc,
    };

    #[derive(Clone)]
    pub struct FrozenAllocator(Arc<Allocator<'static>>);

    // `Allocator` is not `Sync` due to the `RefCell` it contains. But since we do not allow
    // `Allocator` to be accessed there is not way to interact with it and we can safely allow
    // shared access on multiple threads to the expression
    unsafe impl Sync for FrozenAllocator where CExpr<'static>: Sync {}
    unsafe impl Send for FrozenAllocator where CExpr<'static>: Send {}

    #[derive(Clone)]
    pub struct CoreExpr {
        allocator: FrozenAllocator,
        expr: CExpr<'static>,
    }

    impl Eq for CoreExpr {}

    impl PartialEq for CoreExpr {
        fn eq(&self, other: &Self) -> bool {
            ptr::eq(self.expr(), other.expr())
        }
    }

    impl Hash for CoreExpr {
        fn hash<H: Hasher>(&self, h: &mut H) {
            ptr::hash(self.expr(), h)
        }
    }

    impl fmt::Display for CoreExpr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.expr().fmt(f)
        }
    }

    impl fmt::Debug for CoreExpr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.expr().fmt(f)
        }
    }

    impl CoreExpr {
        pub fn new(allocator: FrozenAllocator, expr: CExpr<'static>) -> CoreExpr {
            assert_sync::<Self>();

            CoreExpr { allocator, expr }
        }

        // unsafe: The lifetimes of the returned `Expr` must be bound to `&self`
        pub fn expr<'a>(&'a self) -> CExpr<'a> {
            self.expr
        }

        pub fn with<F, R>(self, f: F) -> R
        where
            F: for<'a, 'b> FnOnce(
                &(dyn Fn(CExpr<'a>) -> CoreExpr + 'b),
                &(dyn Fn(ClosureRef<'a>) -> CoreClosure + 'b),
                CExpr<'a>,
            ) -> R,
        {
            let allocator = &self.allocator;
            f(
                &|expr| {
                    // The lifetime is the same as the one we had in `self` so it is the same
                    // expression or it points into an inner expression
                    unsafe {
                        CoreExpr {
                            allocator: allocator.clone(),
                            expr: mem::transmute::<CExpr, CExpr<'static>>(expr),
                        }
                    }
                },
                &|closure| {
                    // The lifetime is the same as the one we had in `self` so it is the same
                    // expression or it points into an inner expression
                    unsafe {
                        CoreClosure {
                            allocator: allocator.clone(),
                            id: mem::transmute::<&TypedIdent<Symbol>, &'static TypedIdent<Symbol>>(
                                closure.id,
                            ),
                            args: mem::transmute::<
                                &[TypedIdent<Symbol>],
                                &'static [TypedIdent<Symbol>],
                            >(closure.args),
                            expr: mem::transmute::<CExpr, CExpr<'static>>(closure.body),
                        }
                    }
                },
                self.expr(),
            )
        }

        pub fn map(self, f: impl for<'a> FnOnce(CExpr<'a>) -> CExpr<'a>) -> Self {
            CoreExpr {
                allocator: self.allocator,
                expr: f(self.expr),
            }
        }
    }

    #[derive(Clone)]
    pub struct CoreClosure {
        allocator: FrozenAllocator,
        id: &'static TypedIdent<Symbol>,
        args: &'static [TypedIdent<Symbol>],
        expr: CExpr<'static>,
    }

    impl Eq for CoreClosure {}

    impl PartialEq for CoreClosure {
        fn eq(&self, other: &Self) -> bool {
            ptr::eq(self.closure().body, other.closure().body)
        }
    }

    impl Hash for CoreClosure {
        fn hash<H: Hasher>(&self, h: &mut H) {
            ptr::hash(self.closure().body, h)
        }
    }

    impl fmt::Display for CoreClosure {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let ClosureRef { id, args, body } = self.closure();
            write!(
                f,
                "{}@\\{} -> {}",
                id.name,
                args.iter().map(|arg| &arg.name).format(" "),
                body
            )
        }
    }

    impl fmt::Debug for CoreClosure {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let ClosureRef { id, args, body } = self.closure();
            write!(f, "{:?}@\\{:?} -> {:?}", id, args, body)
        }
    }

    impl CoreClosure {
        pub fn new(
            allocator: FrozenAllocator,
            id: &'static TypedIdent<Symbol>,
            args: &'static [TypedIdent<Symbol>],
            expr: CExpr<'static>,
        ) -> CoreClosure {
            assert_sync::<Self>();

            CoreClosure {
                allocator,
                id,
                args,
                expr,
            }
        }

        // unsafe: The lifetimes of the returned `Expr` must be bound to `&self`
        pub fn closure<'a>(&'a self) -> ClosureRef<'a> {
            ClosureRef {
                id: self.id,
                args: self.args,
                body: self.expr,
            }
        }

        pub fn into_expr(self) -> CoreExpr {
            CoreExpr {
                allocator: self.allocator,
                expr: self.expr,
            }
        }

        pub fn map(
            self,
            f: impl for<'a> FnOnce(
                &'a TypedIdent<Symbol>,
                &'a [TypedIdent<Symbol>],
                CExpr<'a>,
            )
                -> (&'a TypedIdent<Symbol>, &'a [TypedIdent<Symbol>], CExpr<'a>),
        ) -> Self {
            let (id, args, expr) = f(self.id, self.args, self.expr);
            CoreClosure {
                allocator: self.allocator,
                id,
                args,
                expr,
            }
        }

        pub fn with<F, R>(self, f: F) -> R
        where
            F: for<'a, 'b> FnOnce(
                &(dyn Fn(CExpr<'a>) -> CoreExpr + 'b),
                &(dyn Fn(ClosureRef<'a>) -> CoreClosure + 'b),
                ClosureRef<'a>,
            ) -> R,
        {
            let allocator = &self.allocator;
            f(
                &|expr| {
                    // The lifetime is the same as the one we had in `self` so it is the same
                    // expression or it points into an inner expression
                    unsafe {
                        CoreExpr {
                            allocator: allocator.clone(),
                            expr: mem::transmute::<CExpr, CExpr<'static>>(expr),
                        }
                    }
                },
                &|closure| {
                    // The lifetime is the same as the one we had in `self` so it is the same
                    // expression or it points into an inner expression
                    unsafe {
                        CoreClosure {
                            allocator: allocator.clone(),
                            id: mem::transmute::<&TypedIdent<Symbol>, &'static TypedIdent<Symbol>>(
                                closure.id,
                            ),
                            args: mem::transmute::<
                                &[TypedIdent<Symbol>],
                                &'static [TypedIdent<Symbol>],
                            >(closure.args),
                            expr: mem::transmute::<CExpr, CExpr<'static>>(closure.body),
                        }
                    }
                },
                self.closure(),
            )
        }
    }

    pub fn freeze_expr<'a>(allocator: &'a Arc<Allocator<'a>>, expr: CExpr<'a>) -> CoreExpr {
        unsafe {
            // Here we temporarily forget the lifetime of `allocator` so it can be moved into a
            // `CoreExpr`. After we have it in `CoreExpr` the expression is then guaranteed to live as
            // long as the `CoreExpr` making it safe again
            CoreExpr::new(
                FrozenAllocator(mem::transmute::<Arc<Allocator>, Arc<Allocator<'static>>>(
                    allocator.clone(),
                )),
                mem::transmute::<CExpr, CExpr<'static>>(expr),
            )
        }
    }

    pub fn freeze_closure<'a>(
        allocator: &'a Arc<Allocator<'a>>,
        id: &'a TypedIdent<Symbol>,
        args: &'a [TypedIdent<Symbol>],
        expr: CExpr<'a>,
    ) -> CoreClosure {
        unsafe {
            // Here we temporarily forget the lifetime of `allocator` so it can be moved into a
            // `CoreClosure`. After we have it in `CoreClusre` the expression is then guaranteed to live as
            // long as the `CoreClosure` making it safe again
            CoreClosure::new(
                FrozenAllocator(mem::transmute::<Arc<Allocator>, Arc<Allocator<'static>>>(
                    allocator.clone(),
                )),
                mem::transmute::<&TypedIdent<Symbol>, &TypedIdent<Symbol>>(id),
                mem::transmute::<&[TypedIdent<Symbol>], &[TypedIdent<Symbol>]>(args),
                mem::transmute::<CExpr, CExpr<'static>>(expr),
            )
        }
    }

    fn assert_sync<T: Sync>() {}
}

pub use self::internal::{freeze_closure, freeze_expr, CoreClosure, CoreExpr};

pub struct Allocator<'a> {
    pub arena: Arena<Expr<'a>>,
    pub alternative_arena: Arena<Alternative<'a>>,
    pub let_binding_arena: Arena<LetBinding<'a>>,
    _marker: ::std::marker::PhantomData<*mut &'a ()>,
}

impl<'a> Allocator<'a> {
    pub fn new() -> Allocator<'a> {
        Allocator {
            arena: Arena::new(),
            alternative_arena: Arena::new(),
            let_binding_arena: Arena::new(),
            _marker: ::std::marker::PhantomData,
        }
    }

    pub fn alloc<T>(&'a self, value: T) -> &'a T
    where
        T: ArenaAllocatable<'a>,
    {
        value.alloc_into(self)
    }

    pub fn alloc_iter<T>(&'a self, iter: impl IntoIterator<Item = T>) -> &'a [T]
    where
        T: ArenaAllocatable<'a>,
    {
        T::alloc_iter_into(iter, self)
    }
}

pub trait ArenaAllocatable<'a>: Sized {
    fn alloc_into(self, allocator: &'a Allocator<'a>) -> &'a Self;
    fn alloc_iter_into(
        iter: impl IntoIterator<Item = Self>,
        allocator: &'a Allocator<'a>,
    ) -> &'a [Self];
}

impl<'a> ArenaAllocatable<'a> for Expr<'a> {
    fn alloc_into(self, allocator: &'a Allocator<'a>) -> &'a Self {
        allocator.arena.alloc(self)
    }

    fn alloc_iter_into(
        iter: impl IntoIterator<Item = Self>,
        allocator: &'a Allocator<'a>,
    ) -> &'a [Self] {
        allocator.arena.alloc_fixed(iter)
    }
}

impl<'a> ArenaAllocatable<'a> for Alternative<'a> {
    fn alloc_into(self, allocator: &'a Allocator<'a>) -> &'a Self {
        allocator.alternative_arena.alloc(self)
    }

    fn alloc_iter_into(
        iter: impl IntoIterator<Item = Self>,
        allocator: &'a Allocator<'a>,
    ) -> &'a [Self] {
        allocator.alternative_arena.alloc_fixed(iter)
    }
}

impl<'a> ArenaAllocatable<'a> for LetBinding<'a> {
    fn alloc_into(self, allocator: &'a Allocator<'a>) -> &'a Self {
        allocator.let_binding_arena.alloc(self)
    }

    fn alloc_iter_into(
        iter: impl IntoIterator<Item = Self>,
        allocator: &'a Allocator<'a>,
    ) -> &'a [Self] {
        allocator.let_binding_arena.alloc_fixed(iter)
    }
}

pub(crate) trait ArenaExt<T> {
    fn alloc_fixed<'a, I>(&'a self, iter: I) -> &'a mut [T]
    where
        I: IntoIterator<Item = T>,
        T: Default;
}

impl<T> ArenaExt<T> for Arena<T> {
    fn alloc_fixed<'a, I>(&'a self, iter: I) -> &'a mut [T]
    where
        I: IntoIterator<Item = T>,
        T: Default,
    {
        use std::{mem::MaybeUninit, ptr};

        let iter = iter.into_iter();

        unsafe {
            struct FillRemainingOnDrop<U: Default> {
                ptr: *mut U,
                end: *mut U,
            }

            impl<U: Default> Drop for FillRemainingOnDrop<U> {
                fn drop(&mut self) {
                    unsafe {
                        while self.ptr != self.end {
                            ptr::write(self.ptr, U::default());
                            self.ptr = self.ptr.add(1);
                        }
                    }
                }
            }
            let (len, max) = iter.size_hint();
            assert!(Some(len) == max);

            let elems = self.alloc_uninitialized(len);

            {
                let elems = elems as *mut _ as *mut MaybeUninit<T>;
                let mut fill = FillRemainingOnDrop {
                    ptr: elems as *mut T,
                    end: elems.add(len) as *mut T,
                };

                for elem in iter {
                    assert!(fill.ptr != fill.end);
                    ptr::write(fill.ptr, elem);
                    fill.ptr = fill.ptr.add(1);
                }
            }

            let elems = elems as *mut _ as *mut [T];
            &mut *elems
        }
    }
}

pub fn with_translator<'e, R>(
    env: &'e dyn PrimitiveEnv<Type = ArcType>,
    f: impl for<'a> FnOnce(&'a Translator<'a, 'e>) -> R,
) -> R {
    let translator = Translator::new(env);
    f(&translator)
}

pub fn with_allocator<R>(f: impl for<'a> FnOnce(&'a Arc<Allocator<'a>>) -> R) -> R {
    let allocator = Arc::new(Allocator::new());
    f(&allocator)
}

pub fn translate(
    env: &dyn PrimitiveEnv<Type = ArcType>,
    expr: &SpannedExpr<'_, Symbol>,
) -> CoreExpr {
    with_translator(env, |translator| {
        freeze_expr(&translator.allocator, translator.translate_alloc(expr))
    })
}

pub struct Translator<'a, 'e> {
    pub allocator: Arc<Allocator<'a>>,

    // Since we merge all patterns that match on the same thing (variants with the same tag,
    // any record or tuple ...), tuple patterns
    // If a field has already been seen in an earlier pattern we must make sure
    // that the variable bound in this pattern/field gets replaced with the
    // symbol from the earlier pattern
    ident_replacements: RefCell<FnvMap<Symbol, Symbol>>,
    env: &'e dyn PrimitiveEnv<Type = ArcType>,
    dummy_symbol: TypedIdent<Symbol>,
    error_symbol: TypedIdent<Symbol>,
    std_prim_symbol: Symbol,
    dummy_record_symbol: TypedIdent<Symbol>,
}

impl<'a, 'e> Translator<'a, 'e> {
    pub fn new(env: &'e dyn PrimitiveEnv<Type = ArcType>) -> Translator<'a, 'e> {
        let hole: ArcType = Type::hole();
        Translator {
            allocator: Arc::new(Allocator::new()),
            ident_replacements: Default::default(),
            env,
            dummy_symbol: TypedIdent {
                name: Symbol::from(""),
                typ: hole.clone(),
            },
            std_prim_symbol: Symbol::from("@std.prim"),
            error_symbol: TypedIdent {
                name: Symbol::from("error"),
                typ: hole.clone(),
            },
            dummy_record_symbol: TypedIdent {
                name: Symbol::from("<record>"),
                typ: hole.clone(),
            },
        }
    }

    pub fn translate_expr(&'a self, expr: &SpannedExpr<'_, Symbol>) -> &'a Expr<'a> {
        struct FixupMatches<'a, 'b> {
            allocator: &'a Allocator<'a>,
            ident_replacments: &'b mut FnvMap<Symbol, Symbol>,
        }

        impl<'a, 'b> Visitor<'a, 'a> for FixupMatches<'a, 'b> {
            type Producer = SameLifetime<'a>;

            fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
                match *expr {
                    Expr::Ident(ref id, span) => {
                        return self.ident_replacments.get(&id.name).map(|new_name| {
                            &*self.allocator.arena.alloc(Expr::Ident(
                                TypedIdent {
                                    name: new_name.clone(),
                                    typ: id.typ.clone(),
                                },
                                span,
                            ))
                        });
                    }

                    Expr::Match(body, alts) if alts.len() == 1 => {
                        // match x with
                        // | y -> EXPR
                        // // ==>
                        // EXPR // with `y`s replaced by `x`
                        match (&alts[0].pattern, body) {
                            (Pattern::Ident(id), Expr::Ident(expr_id, _))
                                if !expr_id.name.is_global() =>
                            {
                                self.ident_replacments
                                    .insert(id.name.clone(), expr_id.name.clone());

                                let expr = alts[0].expr;
                                return Some(self.visit_expr(expr).unwrap_or(expr));
                            }
                            _ => (),
                        }
                    }

                    _ => (),
                }

                walk_expr_alloc(self, expr)
            }

            fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
                Some(self.allocator)
            }
        }

        let expr = self.translate_alloc(expr);

        FixupMatches {
            allocator: &self.allocator,
            ident_replacments: &mut self.ident_replacements.borrow_mut(),
        }
        .visit_expr(expr)
        .unwrap_or(expr)
    }

    fn translate_alloc(&'a self, expr: &SpannedExpr<'_, Symbol>) -> &'a Expr<'a> {
        self.allocator.arena.alloc(self.translate(expr))
    }

    fn translate(&'a self, expr: &SpannedExpr<'_, Symbol>) -> Expr<'a> {
        let mut current = expr;
        let mut lets = Vec::new();
        while let ast::Expr::LetBindings(ref binds, ref tail) = current.value {
            lets.push((current.span.start(), binds));
            current = tail;
        }
        let tail = self.translate_(current);
        lets.iter()
            .rev()
            .fold(tail, |result, &(span_start, ref binds)| {
                self.translate_let(binds, result, span_start)
            })
    }

    fn translate_<'ast>(&'a self, expr: &SpannedExpr<'ast, Symbol>) -> Expr<'a> {
        let arena = &self.allocator.arena;
        match expr.value {
            ast::Expr::App {
                ref implicit_args,
                func: ref function,
                ref args,
            } => {
                let all_args = implicit_args
                    .iter()
                    .chain(&**args)
                    .map(|arg| self.translate(arg));
                match function.value {
                    ast::Expr::Ident(ref id) if is_constructor(&id.name) => {
                        let typ = expr.env_type_of(&self.env);
                        self.new_data_constructor(typ, id, all_args, expr.span)
                    }
                    _ => {
                        let new_args = &*arena.alloc_fixed(all_args);
                        debug_assert!(!new_args.is_empty(), "{:?}", function);
                        Expr::Call(self.translate_alloc(function), new_args)
                    }
                }
            }

            ast::Expr::Array(ref array) => {
                let exprs = arena.alloc_fixed(array.exprs.iter().map(|expr| self.translate(expr)));
                Expr::Data(
                    TypedIdent {
                        name: self.dummy_symbol.name.clone(),
                        typ: array.typ.clone(),
                    },
                    exprs,
                    expr.span.start(),
                )
            }

            ast::Expr::Block(ref exprs) => {
                let (last, prefix) = exprs.split_last().unwrap();
                let result = self.translate(last);
                prefix.iter().rev().fold(result, |result, expr| {
                    Expr::Let(
                        self.allocator.let_binding_arena.alloc(LetBinding {
                            name: self.dummy_symbol.clone(),
                            expr: Named::Expr(self.translate_alloc(expr)),
                            span_start: expr.span.start(),
                        }),
                        arena.alloc(result),
                    )
                })
            }

            ast::Expr::Ident(ref id) => {
                if is_constructor(&id.name) {
                    self.new_data_constructor(id.typ.clone(), id, &mut None.into_iter(), expr.span)
                } else {
                    let name = self
                        .ident_replacements
                        .borrow()
                        .get(&id.name)
                        .unwrap_or(&id.name)
                        .clone();

                    Expr::Ident(
                        TypedIdent {
                            name,
                            typ: id.typ.clone(),
                        },
                        expr.span,
                    )
                }
            }

            ast::Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                let alts = self.allocator.alternative_arena.alloc_fixed(iterator!(
                    Alternative {
                        pattern: Pattern::Constructor(self.bool_constructor(true), vec![]),
                        expr: self.translate_alloc(if_true),
                    },
                    Alternative {
                        pattern: Pattern::Constructor(self.bool_constructor(false), vec![]),
                        expr: self.translate_alloc(if_false),
                    },
                ));
                Expr::Match(self.translate_alloc(pred), alts)
            }

            ast::Expr::Infix {
                ref lhs,
                ref op,
                ref rhs,
                ref implicit_args,
            } => {
                let args = arena.alloc_fixed(
                    implicit_args
                        .iter()
                        .chain(iterator!(&**lhs, &**rhs))
                        .map(|e| self.translate(e)),
                );

                Expr::Call(arena.alloc(Expr::Ident(op.value.clone(), op.span)), args)
            }

            ast::Expr::Lambda(ref lambda) => self.new_lambda(
                expr.span.start(),
                lambda.id.clone(),
                lambda
                    .args
                    .iter()
                    .map(|arg| arg.name.value.clone())
                    .collect(),
                self.translate_alloc(&lambda.body),
                expr.span,
            ),

            ast::Expr::LetBindings(ref binds, ref tail) => {
                self.translate_let(binds, self.translate(tail), expr.span.start())
            }

            ast::Expr::Literal(ref literal) => Expr::Const(Literal::from_ast(literal), expr.span),

            ast::Expr::Match(ref expr, ref alts) => {
                let expr = self.translate_alloc(&**expr);
                let alts: Vec<_> = alts
                    .iter()
                    .map(|alt| Equation {
                        patterns: vec![&alt.pattern],
                        result: self.translate_alloc(&alt.expr),
                    })
                    .collect();
                PatternTranslator(self).translate_top(expr, &alts).clone()
            }
            // expr.projection
            // =>
            // match expr with
            // | { projection } -> projection
            ast::Expr::Projection(ref projected_expr, ref projection, ref projected_type) => {
                let projected_expr = self.translate_alloc(projected_expr);
                self.project_expr(expr.span, projected_expr, projection, projected_type)
            }

            ast::Expr::Record {
                ref typ,
                ref exprs,
                ref base,
                ..
            } => {
                let mut binder = Binder::default();

                // If `base` exists and is non-trivial we need to introduce bindings for each
                // value to ensure that the expressions are evaluated in the correct order
                let needs_bindings = base.as_ref().map_or(false, |base| match base.value {
                    ast::Expr::Ident(_) => false,
                    _ => true,
                });

                let mut last_span = expr.span;
                let mut args = SmallVec::<[_; 16]>::new();
                args.extend(exprs.iter().map(|field| {
                    let expr = match field.value {
                        Some(ref expr) => {
                            last_span = expr.span;
                            self.translate(expr)
                        }
                        None => Expr::Ident(
                            TypedIdent {
                                name: field.name.value.clone(),
                                typ: self.dummy_symbol.typ.clone(),
                            },
                            last_span,
                        ),
                    };
                    if needs_bindings {
                        let typ = expr.env_type_of(&self.env);
                        binder.bind(arena.alloc(expr), typ)
                    } else {
                        expr
                    }
                }));

                let base_binding = base.as_ref().map(|base_expr| {
                    let core_base = self.translate_alloc(base_expr);
                    let typ = remove_aliases_cow(
                        &self.env,
                        &mut NullInterner,
                        &base_expr.env_type_of(&self.env),
                    )
                    .into_owned();

                    let core_base = if needs_bindings {
                        &*arena.alloc(binder.bind(core_base, base_expr.env_type_of(&self.env)))
                    } else {
                        core_base
                    };
                    (core_base, typ)
                });

                if let Some((ref base_ident_expr, ref base_type)) = base_binding {
                    let base_fields: FnvSet<&str> = base_type
                        .row_iter()
                        .map(|field| field.name.declared_name())
                        .collect();

                    let mut reordered_args = SmallVec::<[_; 16]>::new();

                    let mut overridden_fields = FnvMap::default();
                    for (field, arg) in exprs.iter().zip(args.drain(..)) {
                        let field_name = field.name.value.declared_name();
                        if base_fields.contains(field_name) {
                            overridden_fields.insert(field_name, arg);
                        } else {
                            reordered_args.push(arg);
                        }
                    }

                    args.extend(reordered_args);

                    args.extend(base_type.row_iter().map(move |field| {
                        match overridden_fields.remove(field.name.declared_name()) {
                            Some(e) => e,
                            None => self.project_expr(
                                base_ident_expr.span(),
                                base_ident_expr,
                                &field.name,
                                &field.typ,
                            ),
                        }
                    }));
                }

                let record_constructor = Expr::Data(
                    TypedIdent {
                        name: self.dummy_record_symbol.name.clone(),
                        typ: typ.clone(),
                    },
                    arena.alloc_fixed(args),
                    expr.span.start(),
                );
                binder.into_expr(&self.allocator, record_constructor)
            }

            ast::Expr::Tuple { ref elems, .. } => {
                if elems.len() == 1 {
                    self.translate(&elems[0])
                } else {
                    let args = arena.alloc_fixed(elems.iter().map(|expr| self.translate(expr)));
                    Expr::Data(
                        TypedIdent {
                            name: self.dummy_record_symbol.name.clone(),
                            typ: expr.env_type_of(&self.env),
                        },
                        args,
                        expr.span.start(),
                    )
                }
            }

            ast::Expr::TypeBindings(_, ref expr) => self.translate(expr),

            ast::Expr::Do(ast::Do {
                ref id,
                ref bound,
                ref body,
                ref flat_map_id,
                ..
            }) => {
                let flat_map_id = flat_map_id
                    .as_ref()
                    .unwrap_or_else(|| ice!("flat_map_id must be set when translating to core"));

                let mut binder = Binder::default();
                let bound_ident =
                    binder.bind(self.translate_alloc(bound), bound.env_type_of(&self.env));

                let do_id = id.as_ref().map_or_else(
                    || self.dummy_symbol.clone(),
                    |pat| match pat.value {
                        ast::Pattern::Ident(ref id) => id.clone(),
                        _ => TypedIdent {
                            name: Symbol::from("do_bind"),
                            typ: pat.env_type_of(&self.env),
                        },
                    },
                );

                let core_body = self.translate_alloc(body);
                let core_body = match id.as_ref() {
                    Some(Spanned {
                        value: ast::Pattern::Ident(_),
                        ..
                    })
                    | None => core_body,
                    Some(pat) => {
                        let id_expr = self
                            .allocator
                            .arena
                            .alloc(Expr::Ident(do_id.clone(), pat.span));
                        let e = PatternTranslator(self).translate_top(
                            id_expr,
                            &[Equation {
                                patterns: vec![&pat],
                                result: core_body,
                            }],
                        );
                        self.allocator.arena.alloc(e)
                    }
                };

                let lambda = self.new_lambda(
                    expr.span.start(),
                    TypedIdent {
                        name: Symbol::from(format!("do_{}", do_id.name.as_pretty_str())),
                        typ: do_id.typ.clone(),
                    },
                    vec![do_id],
                    core_body,
                    body.span,
                );

                let f = self.translate_alloc(flat_map_id);
                binder.into_expr(
                    &self.allocator,
                    Expr::Call(
                        f,
                        arena.alloc_fixed(Some(lambda).into_iter().chain(Some(bound_ident))),
                    ),
                )
            }

            ast::Expr::MacroExpansion {
                replacement: ref expr,
                ..
            } => self.translate_(expr),

            ast::Expr::Annotated(ref expr, ref typ) => {
                Expr::Cast(arena.alloc(self.translate_(expr)), typ.clone())
            }

            ast::Expr::Error(_) => self.error_expr("Evaluated an invalid exprssion"),
        }
    }

    fn project_expr(
        &'a self,
        span: Span<BytePos>,
        projected_expr: CExpr<'a>,
        projection: &Symbol,
        projected_type: &ArcType,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        // Id should be distinct from the field so bindings aren't shadowed
        let projection_id = Symbol::from(projection.as_str());
        let alt = Alternative {
            pattern: Pattern::Record {
                typ: projected_expr.env_type_of(&self.env),
                fields: vec![(
                    TypedIdent {
                        name: projection_id.clone(),
                        typ: projected_type.clone(),
                    },
                    None,
                )],
            },
            expr: arena.alloc(Expr::Ident(
                TypedIdent {
                    name: projection_id.clone(),
                    typ: projected_type.clone(),
                },
                span,
            )),
        };
        Expr::Match(
            projected_expr,
            self.allocator.alternative_arena.alloc_fixed(once(alt)),
        )
    }

    fn translate_let<'ast>(
        &'a self,
        binds: &ast::ValueBindings<'ast, Symbol>,
        tail: Expr<'a>,
        span_start: BytePos,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;

        if binds.is_recursive() {
            let closures = binds
                .iter()
                .map(|bind| Closure {
                    pos: bind.name.span.start(),
                    name: match bind.name.value {
                        ast::Pattern::Ident(ref id) => id.clone(),
                        _ => unreachable!(),
                    },
                    args: bind.args.iter().map(|arg| arg.name.value.clone()).collect(),
                    expr: self.translate_alloc(&bind.expr),
                })
                .collect::<Vec<_>>();
            Expr::Let(
                self.allocator.let_binding_arena.alloc(LetBinding {
                    // TODO
                    name: self.dummy_symbol.clone(),
                    expr: Named::Recursive(closures),
                    span_start: span_start,
                }),
                arena.alloc(tail),
            )
        } else {
            binds.iter().rev().fold(tail, |tail, bind| {
                let name = match bind.name.value {
                    ast::Pattern::Ident(ref id) => id.clone(),
                    _ => {
                        let bind_expr = self.translate_alloc(&bind.expr);
                        let tail = &*arena.alloc(tail);
                        return PatternTranslator(self).translate_top(
                            bind_expr,
                            &[Equation {
                                patterns: vec![&bind.name],
                                result: tail,
                            }],
                        );
                    }
                };
                let named = if bind.args.is_empty() {
                    Named::Expr(self.translate_alloc(&bind.expr))
                } else {
                    Named::Recursive(vec![Closure {
                        pos: bind.name.span.start(),
                        name: name.clone(),
                        args: bind.args.iter().map(|arg| arg.name.value.clone()).collect(),
                        expr: self.translate_alloc(&bind.expr),
                    }])
                };
                Expr::Let(
                    self.allocator.let_binding_arena.alloc(LetBinding {
                        name: name,
                        expr: named,
                        span_start: bind.expr.span.start(),
                    }),
                    arena.alloc(tail),
                )
            })
        }
    }

    fn bool_constructor(&self, variant: bool) -> TypedIdent<Symbol> {
        let b = self.env.get_bool();
        match *b {
            Type::Alias(ref alias) => match **alias.typ(&mut NullInterner) {
                Type::Variant(ref variants) => TypedIdent {
                    name: variants
                        .row_iter()
                        .nth(variant as usize)
                        .unwrap()
                        .name
                        .clone(),
                    typ: b.clone(),
                },
                _ => ice!(),
            },
            _ => ice!(),
        }
    }

    fn new_data_constructor(
        &'a self,
        expr_type: ArcType,
        id: &TypedIdent<Symbol>,
        new_args: impl IntoIterator<Item = Expr<'a>>,
        span: Span<BytePos>,
    ) -> Expr<'a> {
        self.new_data_constructor_(expr_type, id, &mut new_args.into_iter(), span)
    }

    fn new_data_constructor_(
        &'a self,
        expr_type: ArcType,
        id: &TypedIdent<Symbol>,
        new_args: &mut dyn Iterator<Item = Expr<'a>>,
        span: Span<BytePos>,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        let typ = expr_type;
        let unapplied_args: Vec<_>;
        // If the constructor is not fully applied we retrieve the type of the data
        // by iterating through the arguments. If it is fully applied the arg_iter
        // has no effect and `typ` itself will be used
        let data_type;
        {
            let typ = remove_aliases_cow(&self.env, &mut NullInterner, typ.remove_forall());
            let mut args = arg_iter(typ.remove_forall());
            unapplied_args = args
                .by_ref()
                .enumerate()
                .map(|(i, arg)| TypedIdent {
                    name: Symbol::from(format!("#{}", i)),
                    typ: arg.clone(),
                })
                .collect();
            data_type = args.typ.clone();
        }
        let new_args = new_args.chain(
            unapplied_args
                .iter()
                .map(|arg| Expr::Ident(arg.clone(), span)),
        );
        let data = Expr::Data(
            TypedIdent {
                name: id.name.clone(),
                typ: data_type,
            },
            arena.alloc_fixed(new_args),
            span.start(),
        );
        if unapplied_args.is_empty() {
            data
        } else {
            self.new_lambda(
                span.start(),
                TypedIdent {
                    name: Symbol::from(format!("${}", id.name)),
                    typ: typ,
                },
                unapplied_args,
                arena.alloc(data),
                span,
            )
        }
    }

    fn new_lambda(
        &'a self,
        pos: BytePos,
        name: TypedIdent<Symbol>,
        args: Vec<TypedIdent<Symbol>>,
        body: &'a Expr<'a>,
        span: Span<BytePos>,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        Expr::Let(
            self.allocator.let_binding_arena.alloc(LetBinding {
                name: name.clone(),
                expr: Named::Recursive(vec![Closure {
                    pos,
                    name: name.clone(),
                    args,
                    expr: body,
                }]),
                span_start: span.start(),
            }),
            arena.alloc(Expr::Ident(name, span)),
        )
    }

    fn error_expr(&'a self, msg: &str) -> Expr<'a> {
        let arena = &self.allocator.arena;
        let std_prim_type = self
            .env
            .find_type(&self.std_prim_symbol)
            .unwrap_or_else(|| self.error_symbol.typ.clone());
        let std_prim = arena.alloc(Expr::Ident(
            TypedIdent {
                name: self.std_prim_symbol.clone(),
                typ: std_prim_type.clone(),
            },
            Span::default(),
        ));
        let args = arena.alloc_fixed(
            Some(Expr::Const(Literal::String(msg.into()), Span::default())).into_iter(),
        );
        Expr::Call(
            arena.alloc(self.project_expr(
                Span::default(),
                std_prim,
                &self.error_symbol.name,
                &self.error_symbol.typ,
            )),
            args,
        )
    }
}

impl Typed for Pattern {
    type Ident = Symbol;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType<Symbol>, String> {
        use self::Pattern::*;
        match self {
            Constructor(id, _) | Ident(id) => {
                let mut iter = id.typ.remove_forall().arg_iter();
                for _ in &mut iter {}
                Ok(iter.typ.clone())
            }
            Record { typ, .. } => Ok(typ.clone()),
            Literal(lit) => lit.try_type_of(env),
        }
    }
}

impl<'a> Typed for Expr<'a> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType<Symbol>, String> {
        match self {
            Expr::Call(expr, args) => get_return_type(env, &expr.try_type_of(env)?, args.len()),
            Expr::Const(literal, _) => literal.try_type_of(env),
            Expr::Data(id, ..) => Ok(id.typ.clone()),
            Expr::Ident(id, _) => Ok(id.typ.clone()),
            Expr::Let(_, body) => body.try_type_of(env),
            Expr::Match(_, alts) => alts[0].expr.try_type_of(env),
            Expr::Cast(_, typ) => Ok(typ.clone()),
        }
    }
}

fn get_return_type(
    env: &dyn TypeEnv<Type = ArcType>,
    alias_type: &ArcType,
    arg_count: usize,
) -> Result<ArcType, String> {
    if arg_count == 0 || **alias_type == Type::Hole {
        return Ok(alias_type.clone());
    }
    let function_type = remove_aliases_cow(env, &mut NullInterner, alias_type.remove_forall());

    let ret = function_type
        .remove_forall()
        .as_function()
        .map(|t| Cow::Borrowed(t.1))
        .ok_or_else(|| format!("Unexpected type {} is not a function", function_type))?;

    get_return_type(env, &ret, arg_count - 1)
}

pub struct PatternTranslator<'a, 'e: 'a>(&'a Translator<'a, 'e>);

#[derive(Clone, PartialEq, Debug)]
struct Equation<'a, 'p, 'ast> {
    patterns: Vec<&'p SpannedPattern<'ast, Symbol>>,
    result: &'a Expr<'a>,
}

impl<'a, 'p, 'ast> fmt::Display for Equation<'a, 'p, 'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[({:?},{})]",
            self.patterns.iter().format(", "),
            self.result
        )
    }
}

#[derive(PartialEq)]
enum CType {
    Constructor,
    Record,
    Variable,
    Literal,
}

/// `PatternTranslator` translated nested (AST) patterns into non-nested (core) patterns.
///
/// It does this this by looking at each nested pattern as part of an `Equation` to be solved.
/// Each step of the algorithm looks at the first pattern in each equation, translates it into a
/// a non-nested match and then for each alternative in this created `match` it recursively calls
/// itself with the rest of the equations plus any nested patterns from the pattern that was
/// just translated to the non-nested form.
///
/// For a more comprehensive explanation the following links are recommended
///
/// The implementation of Hob
/// http://marijnhaverbeke.nl/hob/saga/pattern_matching.html
///
/// Derivation of a Pattern-Matching Compiler
/// Geoff Barrett and Philip Wadler
/// Oxford University Computing Laboratory, Programming Research Group
/// 1986
/// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.257.6166&rep=rep1&type=pdf
impl<'a, 'e> PatternTranslator<'a, 'e> {
    fn varcons_compile<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        varcon: CType,
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        match varcon {
            CType::Constructor => self.compile_constructor(default, variables, equations),
            CType::Record => self.compile_record(default, variables, equations),
            CType::Variable => self.compile_variable(default, variables, equations),
            CType::Literal => self.compile_literal(default, variables, equations),
        }
    }

    fn compile_record<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        let new_alt = {
            // Inspect the first pattern of each equation
            // (the rest of the equations are checked recursively)
            let first_iter = || {
                equations
                    .iter()
                    .map(|equation| *equation.patterns.first().unwrap())
            };

            let core_pattern = self.pattern_identifiers(first_iter());

            enum RefOwned<'a, T> {
                Ref(&'a T),
                Owned(T),
            }

            impl<'a, T> std::ops::Deref for RefOwned<'a, T> {
                type Target = T;
                fn deref(&self) -> &T {
                    match self {
                        Self::Ref(x) => x,
                        Self::Owned(x) => x,
                    }
                }
            }

            // Gather the inner patterns so we can prepend them to equations
            let temp = first_iter()
                .map(|pattern| match *unwrap_as(&pattern.value) {
                    ast::Pattern::Record {
                        ref typ,
                        ref fields,
                        ..
                    } => {
                        let mut record_type = None;
                        // Core fields appear in the same order as the normal pattern so we can
                        // get the types from it cheaply
                        let core_fields = match &core_pattern {
                            Pattern::Record { fields, .. } => fields,
                            _ => unreachable!(),
                        };
                        ast::pattern_values(fields)
                            .zip(core_fields)
                            .map(|((name, value), core_field)| {
                                value.as_ref().map(RefOwned::Ref).unwrap_or_else(|| {
                                    let typ = if name.value == core_field.0.name {
                                        core_field.0.typ.clone()
                                    } else {
                                        // If the field has been renamed we need to go the slo path
                                        // and do a lookup but this should be rare
                                        if record_type.is_none() {
                                            record_type = Some(remove_aliases_cow(
                                                &self.0.env,
                                                &mut NullInterner,
                                                typ,
                                            ));
                                        }
                                        record_type
                                            .as_ref()
                                            .unwrap()
                                            .row_iter()
                                            .find(|f| f.name.name_eq(&name.value))
                                            .map(|f| f.typ.clone())
                                            .unwrap_or_else(Type::hole)
                                    };

                                    RefOwned::Owned(spanned(
                                        Span::default(),
                                        ast::Pattern::Ident(TypedIdent {
                                            name: name.value.clone(),
                                            typ,
                                        }),
                                    ))
                                })
                            })
                            .collect::<Vec<_>>()
                    }
                    ast::Pattern::Tuple { ref elems, .. } => {
                        elems.iter().map(RefOwned::Ref).collect::<Vec<_>>()
                    }
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();

            // The first pattern of each equation has been processed, prepend the inner patterns
            // (since those need to be solved first) and then the remaining_patterns
            let new_equations = equations
                .iter()
                .map(|equation| (&equation.patterns[1..], equation.result))
                .zip(&temp)
                .map(|((remaining_equations, result), first)| Equation {
                    patterns: first
                        .iter()
                        .map(|pattern| &**pattern)
                        .chain(remaining_equations.iter().cloned())
                        .collect(),
                    result,
                })
                .collect::<Vec<_>>();

            let new_variables = self.insert_new_variables(&core_pattern, variables);

            let expr = self.translate(default, &new_variables, &new_equations);

            Alternative {
                pattern: core_pattern,
                expr: expr,
            }
        };
        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_fixed(Some(new_alt).into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_constructor<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        let mut group_order = Vec::new();
        let mut groups = HashMap::new();

        for equation in equations {
            match *unwrap_as(&equation.patterns.first().unwrap().value) {
                ast::Pattern::Constructor(ref id, _) => {
                    groups
                        .entry(&id.name)
                        .or_insert_with(|| {
                            group_order.push(&id.name);
                            Vec::new()
                        })
                        .push(equation);
                }
                ast::Pattern::As(_, _)
                | ast::Pattern::Tuple { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Ident(_)
                | ast::Pattern::Literal(_)
                | ast::Pattern::Error => unreachable!(),
            }
        }

        // Check if all the constructors of the variant are matched on

        let complete = {
            let t = variables[0].env_type_of(&self.0.env);
            let t = remove_aliases_cow(&self.0.env, &mut NullInterner, &t);
            let mut iter = t.remove_forall().row_iter();
            groups.len() == iter.by_ref().count() && **iter.current_type() == Type::EmptyRow
        };

        let default_alt = if complete {
            None
        } else {
            Some(Alternative {
                pattern: Pattern::Ident(TypedIdent {
                    name: Symbol::from("_"),
                    typ: self.0.dummy_symbol.typ.clone(),
                }),
                expr: default,
            })
        };

        let new_alts = group_order
            .into_iter()
            .map(|key| {
                let equations = &groups[key];
                let pattern = self.pattern_identifiers(
                    equations
                        .iter()
                        .map(|equation| *equation.patterns.first().unwrap()),
                );

                // Add new patterns for each equation from the nested patterns
                let new_equations = equations
                    .iter()
                    .map(|equation| {
                        let first = match *unwrap_as(&equation.patterns.first().unwrap().value) {
                            ast::Pattern::Constructor(_, ref patterns) => patterns,
                            _ => unreachable!(),
                        };
                        Equation {
                            patterns: first
                                .iter()
                                .chain(equation.patterns.iter().cloned().skip(1))
                                .collect(),
                            result: equation.result,
                        }
                    })
                    .collect::<Vec<_>>();

                let new_variables = self.insert_new_variables(&pattern, variables);

                let expr = self.translate(default, &new_variables, &new_equations);

                Alternative {
                    pattern: pattern,
                    expr: expr,
                }
            })
            .chain(default_alt)
            .collect::<Vec<_>>();
        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_fixed(new_alts.into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_variable<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        let expr = self.translate(
            default,
            &variables[1..],
            &equations
                .iter()
                .map(|equation| Equation {
                    patterns: equation.patterns[1..].to_owned(),
                    result: equation.result,
                })
                .collect::<Vec<_>>(),
        );
        let pattern = self.pattern_identifiers(
            equations
                .iter()
                .map(|equation| *equation.patterns.first().unwrap()),
        );

        let alt = Alternative {
            pattern: pattern,
            expr: expr,
        };

        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_fixed(Some(alt).into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_literal<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        let mut group_order = Vec::new();
        let mut groups = HashMap::new();

        for equation in equations {
            match *unwrap_as(&equation.patterns.first().unwrap().value) {
                ast::Pattern::Literal(ref literal) => {
                    groups
                        .entry(literal)
                        .or_insert_with(|| {
                            group_order.push(literal);
                            Vec::new()
                        })
                        .push(equation.clone());
                }
                ast::Pattern::Constructor(_, _)
                | ast::Pattern::As(_, _)
                | ast::Pattern::Tuple { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Ident(_)
                | ast::Pattern::Error => unreachable!(),
            }
        }

        let default_alt = Alternative {
            pattern: Pattern::Ident(self.0.dummy_symbol.clone()),
            expr: default,
        };

        let new_alts = group_order
            .into_iter()
            .map(|key| {
                let equations = &groups[key];
                let pattern = Pattern::Literal(Literal::from_ast(key));

                let new_equations = equations
                    .iter()
                    .map(|equation| Equation {
                        patterns: equation.patterns.iter().cloned().skip(1).collect(),
                        result: equation.result,
                    })
                    .collect::<Vec<_>>();

                let new_variables = self.insert_new_variables(&pattern, variables);
                let expr = self.translate(default, &new_variables, &new_equations);
                Alternative {
                    pattern: pattern,
                    expr: expr,
                }
            })
            .chain(Some(default_alt))
            .collect::<Vec<_>>();

        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_fixed(new_alts.into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    // Generates a variable for each of the new equations we inserted
    // This variable is what we `match` the expression(s) on
    fn insert_new_variables(
        &self,
        pattern: &Pattern,
        variables: &[&'a Expr<'a>],
    ) -> Vec<&'a Expr<'a>> {
        PatternIdentifiers::new(pattern)
            .map(|id| {
                &*self
                    .0
                    .allocator
                    .arena
                    .alloc(Expr::Ident(id, Span::default()))
            })
            .chain(variables[1..].iter().cloned())
            .collect::<Vec<_>>()
    }

    fn translate_top<'p>(
        &mut self,
        expr: &'a Expr<'a>,
        equations: &[Equation<'a, 'p, '_>],
    ) -> Expr<'a> {
        let arena = &self.0.allocator.arena;
        let default = arena.alloc(self.0.error_expr("Unmatched pattern"));
        match *expr {
            Expr::Ident(..) => self.translate(default, &[expr], equations).clone(),
            _ => {
                let name = TypedIdent {
                    name: Symbol::from("match_pattern"),
                    typ: expr.env_type_of(&self.0.env),
                };
                let id_expr = self
                    .0
                    .allocator
                    .arena
                    .alloc(Expr::Ident(name.clone(), expr.span()));
                Expr::Let(
                    self.0.allocator.let_binding_arena.alloc(LetBinding {
                        name: name,
                        expr: Named::Expr(expr),
                        span_start: expr.span().start(),
                    }),
                    self.translate(default, &[id_expr], equations),
                )
            }
        }
    }

    fn translate<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p, '_>],
    ) -> &'a Expr<'a> {
        fn varcon(pattern: &ast::Pattern<Symbol>) -> CType {
            match *pattern {
                ast::Pattern::As(_, ref pattern) => varcon(&pattern.value),
                ast::Pattern::Ident(_) => CType::Variable,
                ast::Pattern::Record { .. } | ast::Pattern::Tuple { .. } => CType::Record,
                ast::Pattern::Constructor(_, _) => CType::Constructor,
                ast::Pattern::Literal(_) => CType::Literal,
                ast::Pattern::Error => ice!("ICE: Error pattern survived typechecking"),
            }
        }

        let mut binder = Binder::default();

        // The equations must be processed by group
        //
        // | Some (Some x) ->
        // | Some None ->
        // | x ->
        let groups = equations
            .iter()
            .group_by(|equation| varcon(&equation.patterns.first().expect("Pattern").value));

        let expr = match variables.first() {
            None => equations
                .first()
                .map(|equation| equation.result)
                .unwrap_or(default),
            Some(_) => {
                fn bind_variables<'b>(
                    env: &dyn PrimitiveEnv<Type = ArcType>,
                    pat: &ast::SpannedPattern<'_, Symbol>,
                    variable: CExpr<'b>,
                    binder: &mut Binder<'b>,
                ) {
                    match pat.value {
                        ast::Pattern::As(ref id, ref pat) => {
                            binder.bind_id(
                                TypedIdent {
                                    name: id.value.clone(),
                                    typ: pat.env_type_of(&env),
                                },
                                variable,
                            );
                            bind_variables(env, pat, variable, binder);
                        }
                        ast::Pattern::Record {
                            implicit_import: Some(ref implicit_import),
                            ..
                        } => {
                            binder.bind_id(
                                TypedIdent {
                                    name: implicit_import.value.clone(),
                                    typ: pat.env_type_of(&env),
                                },
                                variable,
                            );
                        }
                        _ => (),
                    }
                }
                // Extract the identifier from each `id@PATTERN` and bind it with `let` before this match
                {
                    for equation in equations {
                        let pat = equation.patterns.first().expect("Pattern");
                        bind_variables(
                            self.0.env,
                            pat,
                            variables.first().expect("Variable"),
                            &mut binder,
                        );
                    }
                }

                let groups = (&groups).into_iter().collect::<Vec<_>>();
                groups
                    .into_iter()
                    .rev()
                    .fold(default, |expr, (key, group)| {
                        let equation_group = group.cloned().collect::<Vec<_>>();
                        self.varcons_compile(expr, variables, key, &equation_group)
                    })
            }
        };
        debug!(
            "Translated: [{}]\n[{}]\nInto: {}",
            variables.iter().format(",\n"),
            equations.iter().format(",\n"),
            expr
        );
        let allocator = &self.0.allocator;
        binder.into_expr_ref(allocator, expr)
    }

    fn extract_ident(&self, index: usize, pattern: &ast::Pattern<Symbol>) -> TypedIdent<Symbol> {
        get_ident(pattern).unwrap_or_else(|| TypedIdent {
            name: Symbol::from(format!("pattern_{}", index)),
            typ: pattern.env_type_of(&self.0.env),
        })
    }

    // Gather all the identifiers of top level pattern of each of the `patterns` and create a core
    // pattern.
    // Nested patterns are ignored here.
    fn pattern_identifiers<'b, 'p: 'b, 'ast, I>(&self, patterns: I) -> Pattern
    where
        I: IntoIterator<Item = &'b SpannedPattern<'ast, Symbol>>,
        'ast: 'b,
    {
        self.pattern_identifiers_(&mut patterns.into_iter())
    }

    fn pattern_identifiers_<'b, 'p: 'b, 'ast>(
        &self,
        patterns: &mut dyn Iterator<Item = &'b SpannedPattern<'ast, Symbol>>,
    ) -> Pattern {
        let mut identifiers: Vec<TypedIdent<Symbol>> = Vec::new();
        let mut record_fields: Vec<(TypedIdent<Symbol>, _)> = Vec::new();
        let mut core_pattern = None;

        let mut replacements = self.0.ident_replacements.borrow_mut();

        fn add_duplicate_ident(
            replacements: &mut FnvMap<Symbol, Symbol>,
            record_fields: &mut Vec<(TypedIdent<Symbol>, Option<Symbol>)>,
            field: &Symbol,
            pattern: Option<&SpannedPattern<'_, Symbol>>,
        ) -> bool {
            match record_fields.iter().find(|id| id.0.name == *field).cloned() {
                Some(earlier_var) => {
                    let duplicate = match pattern {
                        Some(ref pattern) => get_ident(&pattern.value).map(|id| id.name),
                        None => Some(field.clone()),
                    };
                    if let Some(duplicate) = duplicate {
                        replacements.insert(duplicate, earlier_var.1.unwrap_or(earlier_var.0.name));
                    }
                    true
                }
                None => false,
            }
        }

        let mut match_type = None;

        for pattern in patterns {
            match *unwrap_as(&pattern.value) {
                ast::Pattern::Constructor(ref id, ref patterns) => {
                    core_pattern = Some(Pattern::Constructor(id.clone(), Vec::new()));

                    for (i, pattern) in patterns.iter().enumerate() {
                        match identifiers.get(i).map(|i| i.name.clone()) {
                            Some(earlier_var) => {
                                if let Some(duplicate) = get_ident(&pattern.value).map(|id| id.name)
                                {
                                    replacements.insert(duplicate, earlier_var);
                                }
                            }
                            None => identifiers.push(self.extract_ident(i, &pattern.value)),
                        }
                    }
                }
                ast::Pattern::As(..) => unreachable!(),
                ast::Pattern::Ident(ref id) => {
                    if core_pattern.is_none() {
                        core_pattern = Some(Pattern::Ident(id.clone()));
                    }
                }
                ast::Pattern::Tuple { ref typ, ref elems } => {
                    let typ = remove_aliases_cow(&self.0.env, &mut NullInterner, typ);

                    for (i, (elem, field_type)) in elems.iter().zip(typ.row_iter()).enumerate() {
                        if !add_duplicate_ident(
                            &mut replacements,
                            &mut record_fields,
                            &field_type.name,
                            Some(elem),
                        ) {
                            record_fields.push((
                                TypedIdent {
                                    name: field_type.name.clone(),
                                    typ: field_type.typ.clone(),
                                },
                                Some(self.extract_ident(i, &elem.value).name),
                            ));
                        }
                    }
                }
                // Records need to merge the bindings of each of the patterns as we want the core
                // `match` expression to just have one alternative
                //
                // | { x, y = a } -> ..
                // | { z = Some w } -> ...
                // // Binds [x, a, z] as we need to turn this into
                // | { x = x, y = a, z = z } -> match z with ...
                // ```
                ast::Pattern::Record {
                    ref typ,
                    ref fields,
                    ..
                } => {
                    let typ = remove_aliases_cow(&self.0.env, &mut NullInterner, typ);
                    match_type = Some(typ.clone());

                    for (i, (name, value)) in ast::pattern_values(fields).enumerate() {
                        if !add_duplicate_ident(
                            &mut replacements,
                            &mut record_fields,
                            &name.value,
                            value.as_ref(),
                        ) {
                            let x = value
                                .as_ref()
                                .map(|pattern| self.extract_ident(i, &pattern.value).name);
                            let field_type = typ
                                .row_iter()
                                .find(|f| f.name.name_eq(&name.value))
                                .map(|f| f.typ.clone())
                                .unwrap_or_else(|| Type::hole());
                            record_fields.push((
                                TypedIdent {
                                    name: name.value.clone(),
                                    typ: field_type,
                                },
                                x,
                            ));
                        }
                    }
                }
                ast::Pattern::Literal(_) | ast::Pattern::Error => (),
            }
        }

        match core_pattern {
            Some(mut p) => {
                if let Pattern::Constructor(_, ref mut ids) = p {
                    *ids = identifiers
                }
                p
            }
            None => Pattern::Record {
                typ: match_type.unwrap_or_default().into_owned(),
                fields: record_fields,
            },
        }
    }
}

fn get_ident(pattern: &ast::Pattern<Symbol>) -> Option<TypedIdent<Symbol>> {
    match *pattern {
        ast::Pattern::Ident(ref id) => Some(id.clone()),
        ast::Pattern::As(_, ref pat) => get_ident(&pat.value),
        _ => None,
    }
}

fn unwrap_as<'a, 'ast>(pattern: &'a ast::Pattern<'ast, Symbol>) -> &'a ast::Pattern<'ast, Symbol> {
    match *pattern {
        ast::Pattern::As(_, ref pattern) => unwrap_as(&pattern.value),
        _ => pattern,
    }
}

struct PatternIdentifiers<'a> {
    pattern: &'a Pattern,
    start: usize,
    end: usize,
}

impl<'a> PatternIdentifiers<'a> {
    pub fn new(pattern: &'a Pattern) -> PatternIdentifiers<'a> {
        PatternIdentifiers {
            pattern: pattern,
            start: 0,
            end: match *pattern {
                Pattern::Constructor(_, ref patterns) => patterns.len(),
                Pattern::Record { ref fields, .. } => fields.len(),
                Pattern::Ident(_) | Pattern::Literal(_) => 0,
            },
        }
    }
}

impl<'a> Iterator for PatternIdentifiers<'a> {
    type Item = TypedIdent<Symbol>;

    fn next(&mut self) -> Option<Self::Item> {
        match *self.pattern {
            Pattern::Constructor(_, ref patterns) => {
                if self.start < self.end {
                    let i = self.start;
                    self.start += 1;
                    Some(patterns[i].clone())
                } else {
                    None
                }
            }
            Pattern::Record { ref fields, .. } => {
                if self.start < fields.len() {
                    let field = &fields[self.start];
                    self.start += 1;
                    Some(
                        field
                            .1
                            .as_ref()
                            .map(|name| TypedIdent {
                                name: name.clone(),
                                typ: field.0.typ.clone(),
                            })
                            .unwrap_or_else(|| field.0.clone()),
                    )
                } else {
                    None
                }
            }
            Pattern::Ident(_) | Pattern::Literal(_) => None,
        }
    }
}

impl<'a> DoubleEndedIterator for PatternIdentifiers<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match *self.pattern {
            Pattern::Constructor(_, ref patterns) => {
                if self.start != self.end {
                    self.end -= 1;
                    Some(patterns[self.end].clone())
                } else {
                    None
                }
            }
            Pattern::Record { ref fields, .. } => {
                if self.start != self.end {
                    self.end -= 1;
                    let field = &fields[self.end];
                    Some(
                        field
                            .1
                            .as_ref()
                            .map(|name| TypedIdent {
                                name: name.clone(),
                                typ: field.0.typ.clone(),
                            })
                            .unwrap_or_else(|| field.0.clone()),
                    )
                } else {
                    None
                }
            }
            Pattern::Ident(_) | Pattern::Literal(_) => None,
        }
    }
}

impl<'a> ExactSizeIterator for PatternIdentifiers<'a> {
    fn len(&self) -> usize {
        self.end - self.start
    }
}

pub(crate) fn is_primitive(name: &Symbol) -> bool {
    let name = name.as_str();
    name == "&&" || name == "||" || name.starts_with('#')
}

#[cfg(any(test, feature = "test"))]
pub mod tests {
    extern crate gluon_parser as parser;

    use super::*;

    use std::collections::HashMap;

    use codespan_reporting::files::Files;

    use crate::base::{
        ast, pos,
        source::Source,
        symbol::{Symbol, SymbolModule, Symbols},
        types::TypeCache,
    };

    use crate::{
        core::grammar::ExprParser,
        vm::{RootedThread, Thread},
    };

    fn parse_expr(symbols: &mut Symbols, expr_str: &str) -> ast::RootExpr<Symbol> {
        base::mk_ast_arena!(arena);
        let expr = arena.alloc(
            self::parser::parse_expr(
                arena.borrow(),
                &mut SymbolModule::new("".into(), symbols),
                &TypeCache::new(),
                expr_str,
            )
            .unwrap(),
        );

        struct Visitor<'ast>(&'ast ast::Arena<'ast, Symbol>);

        impl<'ast> ast::MutVisitor<'_, 'ast> for Visitor<'ast> {
            type Ident = Symbol;
            fn visit_expr(&mut self, expr: &mut SpannedExpr<'ast, Symbol>) {
                match &mut expr.value {
                    ast::Expr::Do(d) => {
                        d.flat_map_id = Some(self.0.alloc(pos::spanned(
                            expr.span,
                            ast::Expr::Ident(TypedIdent::new(Symbol::from("flat_map"))),
                        )))
                    }
                    _ => (),
                }
                ast::walk_mut_expr(self, expr);
            }
        }

        ast::MutVisitor::visit_expr(&mut Visitor(&arena), expr);

        ast::RootExpr::new(arena.clone(), expr)
    }

    pub struct PatternEq<'a>(pub &'a Expr<'a>);

    impl<'a> fmt::Debug for PatternEq<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.0.fmt(f)
        }
    }

    impl<'a> fmt::Display for PatternEq<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<'a> PartialEq<Expr<'a>> for PatternEq<'a> {
        fn eq(&self, other: &Expr<'a>) -> bool {
            let mut map = HashMap::new();
            expr_eq(&mut map, self.0, other)
        }
    }

    fn check(map: &mut HashMap<Symbol, Symbol>, l: &Symbol, r: &Symbol) -> bool {
        let l = map.entry(l.clone()).or_insert_with(|| r.clone());
        if l != r {
            error!("{:#?} == {:#?}", l, r);
        }
        l == r
    }

    fn expr_eq(map: &mut HashMap<Symbol, Symbol>, l: &Expr, r: &Expr) -> bool {
        let b = expr_eq_(map, l, r);
        if !b {
            eprintln!("{} != {}", l, r);
        }
        b
    }

    fn expr_eq_(map: &mut HashMap<Symbol, Symbol>, l: &Expr, r: &Expr) -> bool {
        match (l, r) {
            (&Expr::Match(_, l_alts), &Expr::Match(_, r_alts)) => {
                for (l, r) in l_alts.iter().zip(r_alts) {
                    let eq = match (&l.pattern, &r.pattern) {
                        (
                            &Pattern::Constructor(ref l, ref l_ids),
                            &Pattern::Constructor(ref r, ref r_ids),
                        ) => {
                            check(map, &l.name, &r.name)
                                && l_ids
                                    .iter()
                                    .zip(r_ids)
                                    .all(|(l, r)| check(map, &l.name, &r.name))
                        }
                        (&Pattern::Ident(ref l), &Pattern::Ident(ref r)) => {
                            check(map, &l.name, &r.name)
                        }
                        (
                            &Pattern::Record { fields: ref l, .. },
                            &Pattern::Record { fields: ref r, .. },
                        ) => l.iter().zip(r).all(|(l, r)| {
                            check(map, &l.0.name, &r.0.name)
                                && match (&l.1, &r.1) {
                                    (&Some(ref l), &Some(ref r)) => check(map, l, r),
                                    (&None, &None) => true,
                                    _ => false,
                                }
                        }),
                        (&Pattern::Literal(ref l_literal), &Pattern::Literal(ref r_literal)) => {
                            l_literal == r_literal
                        }
                        _ => false,
                    };
                    if !eq || !expr_eq(map, &l.expr, &r.expr) {
                        return false;
                    }
                }
                true
            }
            (&Expr::Const(ref l, _), &Expr::Const(ref r, _)) => l == r,
            (&Expr::Ident(ref l, _), &Expr::Ident(ref r, _)) => check(map, &l.name, &r.name),
            (&Expr::Let(ref lb, l), &Expr::Let(ref rb, r)) => {
                let b = match (&lb.expr, &rb.expr) {
                    (Named::Expr(le), Named::Expr(re)) => expr_eq(map, le, re),
                    (Named::Recursive(lcs), Named::Recursive(rcs)) => {
                        lcs.len() == rcs.len()
                            && lcs.iter().zip(rcs).all(|(lc, rc)| {
                                check(map, &lc.name.name, &rc.name.name)
                                    && lc.args.len() == rc.args.len()
                                    && lc
                                        .args
                                        .iter()
                                        .zip(&rc.args)
                                        .all(|(l, r)| check(map, &l.name, &r.name))
                                    && expr_eq(map, &lc.expr, &rc.expr)
                            })
                    }
                    _ => false,
                };
                check(map, &lb.name.name, &rb.name.name) && b && expr_eq(map, l, r)
            }
            (&Expr::Call(lf, l_args), &Expr::Call(rf, r_args)) => {
                expr_eq(map, lf, rf)
                    && l_args.len() == r_args.len()
                    && l_args.iter().zip(r_args).all(|(l, r)| expr_eq(map, l, r))
            }
            (&Expr::Data(ref l, l_args, ..), &Expr::Data(ref r, r_args, ..)) => {
                check(map, &l.name, &r.name)
                    && l_args.len() == r_args.len()
                    && l_args.iter().zip(r_args).all(|(l, r)| expr_eq(map, l, r))
            }
            _ => false,
        }
    }

    pub fn check_translation(expr_str: &str, expected_str: &str) {
        let vm = RootedThread::new();
        check_translation_with(&vm, expr_str, expected_str, |_, e| e)
    }

    pub fn check_translation_with(
        vm: &Thread,
        expr_str: &str,
        expected_str: &str,
        post: impl for<'a> FnOnce(&'a Allocator<'a>, CExpr<'a>) -> CExpr<'a>,
    ) {
        #[cfg(test)]
        let _ = ::env_logger::try_init();

        let mut symbols = Symbols::new();

        let env = vm.get_env();
        let translator = Translator::new(&env);

        let expr = parse_expr(&mut symbols, expr_str);
        let core_expr = translator.translate_expr(&expr.expr());
        let core_expr = post(&translator.allocator, core_expr);

        check_expr_eq(core_expr, expected_str);
    }

    pub fn check_expr_eq(core_expr: CExpr, expected_str: &str) {
        let mut symbols = Symbols::new();

        let allocator = Allocator::new();

        let expected_expr = ExprParser::new()
            .parse(&mut symbols, &allocator, expected_str)
            .unwrap_or_else(|err| {
                let filemap = crate::base::source::FileMap::new("test".into(), expected_str.into());
                panic!(
                    "{}",
                    err.map_location(|i| {
                        let location =
                            Source::location(&filemap, codespan::ByteIndex::from(i as u32))
                                .unwrap();
                        let line_span = filemap.line_range((), location.line.to_usize()).unwrap();
                        format!(
                            "line {}, column {}\n{}{}^",
                            location.line.number(),
                            location.column.number(),
                            &filemap.source()[line_span],
                            " ".repeat(location.column.0 as usize),
                        )
                    })
                )
            });
        assert_deq!(PatternEq(&core_expr), expected_expr);
    }

    #[test]
    fn match_expr() {
        let expr_str = r#"
            let test = 1
            in
            match test with
            | x -> x
        "#;

        let expected_str = " let y = 1 in y ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn nested_match_expr() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor x) -> x
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor x -> x
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn multiple_alternatives_nested_match_expr() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor x) -> 1
            | Ctor y -> 2
            | z -> 3
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor x -> 1
                | y -> 2
                end
            | z -> 3
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn translate_equality_match() {
        let expr_str = r#"
            match m with
            | { l = Some l_val, r = Some r_val } -> eq l_val r_val
            | { l = None, r = None } -> True
            | _ -> False
        "#;

        let expected_str = r#"
            match m with
            | { l = l1, r = r1 } ->
                match l1 with
                | Some l_val ->
                    match r1 with
                    | Some r_val -> eq l_val r_val
                    | _1 -> False
                    end
                | None ->
                    match r1 with
                    | None -> True
                    | _2 -> False
                    end
                | _3 -> False
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern() {
        let expr_str = r#"
            match test with
            | x@Test -> x
            | y -> y
        "#;

        let expected_str = "
            let x = test in
            match x with
            | Test -> x
            | _ -> test
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_on_non_identifier() {
        let expr_str = r#"
            match 1 with
            | x@Test -> x
            | y -> y
        "#;

        let expected_str = "
            let match_pattern = 1 in
            let x = match_pattern in
            match x with
            | Test -> x
            | _ -> match_pattern
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_multiple() {
        let expr_str = r#"
            match test with
            | x@Test -> x
            | y@Test2 -> y
            | z -> z
        "#;

        let expected_str = "
            let x = test in
            let y = test in
            match test with
            | Test -> x
            | Test2 -> y
            | _ -> test
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_nested() {
        let expr_str = r#"
            match test with
            | { z = x@Test } -> x
        "#;

        let expected_str = "
            match test with
            | { z = z } ->
                let x = z in
                match z with
                | Test -> x
                end
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn let_as_pattern_record() {
        let expr_str = r#"
            let x@{ y } = test
            x
        "#;

        let expected_str = "
            let x = test in
            match x with
            | { y } -> x
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn let_as_pattern_identifier() {
        let expr_str = r#"
            let x@y = 1
            y
        "#;

        let expected_str = "
            let match_pattern = 1 in
            let x = match_pattern in
            match_pattern
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_int_literal() {
        let expr_str = r#"
            match 2 with
            | 1 -> "one"
            | _ -> "any"
        "#;

        let expected_str = r#"
            let match_pattern = 2 in
            match match_pattern with
            | 1 -> "one"
            | _ -> "any"
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_string_literal() {
        let expr_str = r#"
            let x = "zero" in
            match x with
            | "one" -> 1
            | _ -> 0
        "#;

        let expected_str = r#"
            let x = "zero" in
            match x with
            | "one" -> 1
            | _ -> 0
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_literal_pattern() {
        let expr_str = r#"
            match 2 with
            | x@2 -> x
            | _ -> 0
        "#;

        let expected_str = r#"
            let p = 2 in
            let x = p in
            match p with
            | 2 -> x
            | _ -> 0
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn multiple_alternatives_nested_match_expr_with_literal() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor 4) -> 1
            | Ctor y -> 2
            | z -> 3
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor p2 ->
                    match p2 with
                    | 4 -> 1
                    end
                | y -> 2
                end
            | z -> 3
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_record_with_literal() {
        let expr_str = r#"
            match { x = 2, y = 3 } with
            | { x = 2, y = 3 } -> "4"
            | _ -> "6"
        "#;

        let expected_str = r#"
            let p = { x = 2, y = 3 } in
            match p with
            | { x = x, y = y } ->
                match x with
                | 2 ->
                    match y with
                    | 3 -> "4"
                    | _ -> "6"
                    end
                | _ -> "6"
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_constructor_with_literal() {
        let expr_str = r#"
            match Test 2 with
            | Other -> 0
            | _ -> 2
        "#;

        let expected_str = r#"
            let p = Test 2 in
            match p with
            | Other -> 0
            | _ -> 2
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_constructor_with_mutliple_literals() {
        let expr_str = r#"
            type Test = | Test Int String
            match Test 2 "hello" with
            | Test 2 "hello" -> 0
            | _ -> 2
        "#;

        let expected_str = r#"
            let p = Test 2 "hello" in
            match p with
            | Test p0 p1 ->
                match p0 with
                | 2 ->
                    match p1 with
                    | "hello" -> 0
                    | _ -> 2
                    end
                | _ -> 2
                end
            | _ -> 2
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn do_expression_with_pattern() {
        let expr_str = r#"
            do { test } = record_action
            wrap test
        "#;

        let expected_str = r#"
            let bind_arg = record_action in
            flat_map (
                rec let f arg =
                    match arg with
                    | { test } -> wrap test
                    end
                in
                f)
                bind_arg
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn expr_size() {
        let s = std::mem::size_of::<Expr>();
        assert!(s <= 40, "{} is to large for expressions", s);
    }
}
