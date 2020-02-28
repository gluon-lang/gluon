//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)
use std::{
    borrow::Cow,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    slice,
};

use either::Either;

use itertools::Itertools;

use crate::metadata::{Comment, Metadata};
use crate::pos::{self, BytePos, HasSpan, Span, Spanned};
use crate::resolve::remove_aliases_cow;
use crate::symbol::Symbol;
use crate::types::{
    self, Alias, AliasData, ArcType, ArgType, Flags, NullInterner, Type, TypeEnv, TypeExt,
};
use ordered_float::NotNan;

pub trait DisplayEnv {
    type Ident;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str;
}

pub trait IdentEnv: DisplayEnv {
    fn from_str(&mut self, s: &str) -> Self::Ident;
}

pub struct EmptyEnv<T>(PhantomData<T>);
impl<T> Default for EmptyEnv<T> {
    fn default() -> Self {
        EmptyEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for EmptyEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<'t, T: ?Sized + DisplayEnv> DisplayEnv for &'t T {
    type Ident = T::Ident;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        (**self).string(ident)
    }
}

impl<'t, T: ?Sized + DisplayEnv> DisplayEnv for &'t mut T {
    type Ident = T::Ident;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        (**self).string(ident)
    }
}

impl<'a, T: ?Sized + IdentEnv> IdentEnv for &'a mut T {
    fn from_str(&mut self, s: &str) -> Self::Ident {
        (**self).from_str(s)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct InnerAstType<Id> {
    metadata: Option<Metadata>,
    typ: Spanned<Type<Id, AstType<Id>>, BytePos>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AstType<Id> {
    _typ: Box<InnerAstType<Id>>,
}

impl<Id> Deref for AstType<Id> {
    type Target = Type<Id, AstType<Id>>;

    fn deref(&self) -> &Self::Target {
        &self._typ.typ.value
    }
}

impl<Id> DerefMut for AstType<Id> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self._typ.typ.value
    }
}

impl<Id: AsRef<str>> fmt::Display for AstType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", types::TypeFormatter::new(self))
    }
}

impl<Id> From<Spanned<Type<Id, AstType<Id>>, BytePos>> for AstType<Id> {
    fn from(typ: Spanned<Type<Id, AstType<Id>>, BytePos>) -> Self {
        AstType {
            _typ: Box::new(InnerAstType {
                metadata: None,
                typ,
            }),
        }
    }
}

impl<Id> From<Type<Id, AstType<Id>>> for AstType<Id> {
    fn from(typ: Type<Id, AstType<Id>>) -> Self {
        Self::from(pos::spanned2(0.into(), 0.into(), typ))
    }
}

impl<Id> From<(Type<Id, AstType<Id>>, Flags)> for AstType<Id> {
    fn from((typ, _): (Type<Id, AstType<Id>>, Flags)) -> AstType<Id> {
        Self::from(typ)
    }
}

impl<Id> HasSpan for AstType<Id> {
    fn span(&self) -> Span<BytePos> {
        self._typ.typ.span
    }
}

impl<Id> TypeExt for AstType<Id>
where
    Id: Clone,
{
    type Id = Id;

    fn new(typ: Type<Id, Self>) -> Self {
        Self::from(typ)
    }

    fn strong_count(_typ: &Self) -> usize {
        1
    }
}

pub trait HasMetadata {
    fn metadata(&self) -> Option<&Metadata>;

    fn comment(&self) -> Option<&Comment> {
        self.metadata()
            .and_then(|metadata| metadata.comment.as_ref())
    }
}

impl<Id> HasMetadata for AstType<Id> {
    fn metadata(&self) -> Option<&Metadata> {
        self._typ.metadata.as_ref()
    }
}

impl<Id> AstType<Id> {
    pub fn with_metadata<T>(metadata: T, typ: Spanned<Type<Id, AstType<Id>>, BytePos>) -> Self
    where
        T: Into<Option<Metadata>>,
    {
        AstType {
            _typ: Box::new(InnerAstType {
                metadata: metadata.into(),
                typ,
            }),
        }
    }

    pub fn set_metadata<T>(&mut self, metadata: T)
    where
        T: Into<Option<Metadata>>,
    {
        self._typ.metadata = metadata.into();
    }

    pub fn into_inner(self) -> Type<Id, Self> {
        self._typ.typ.value
    }

    pub fn remove_single_forall(&mut self) -> &mut AstType<Id> {
        match self._typ.typ.value {
            Type::Forall(_, ref mut typ) => typ,
            _ => self,
        }
    }
}

impl<Id> AsMut<SpannedAstType<Id>> for AstType<Id> {
    fn as_mut(&mut self) -> &mut SpannedAstType<Id> {
        &mut self._typ.typ
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct TypedIdent<Id = Symbol, T = ArcType<Id>> {
    pub typ: T,
    pub name: Id,
}

impl<Id> TypedIdent<Id> {
    pub fn new(name: Id) -> TypedIdent<Id>
    where
        Id: PartialEq,
    {
        TypedIdent {
            typ: Type::hole(),
            name,
        }
    }
}

impl<Id, T> TypedIdent<Id, T> {
    pub fn new2(name: Id, typ: T) -> TypedIdent<Id, T> {
        TypedIdent { name, typ }
    }
}

impl<Id, T> AsRef<str> for TypedIdent<Id, T>
where
    Id: AsRef<str>,
{
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Literal {
    Byte(u8),
    Int(i64),
    Float(NotNan<f64>),
    String(String),
    Char(char),
}

/// Pattern which contains a location
pub type SpannedPattern<'ast, Id> = Spanned<Pattern<'ast, Id>, BytePos>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct PatternField<Id, P> {
    pub name: Spanned<Id, BytePos>,
    pub value: Option<P>,
}

#[derive(Eq, PartialEq, Debug)]
pub enum Pattern<'ast, Id> {
    /// An as-pattern, eg. `option @ { monoid, functor }`
    As(Spanned<Id, BytePos>, &'ast mut SpannedPattern<'ast, Id>),
    /// Constructor pattern, eg. `Cons x xs`
    Constructor(TypedIdent<Id>, &'ast mut [SpannedPattern<'ast, Id>]),
    /// Ident pattern, eg: `x`
    Ident(TypedIdent<Id>),
    /// Record pattern, eg. `{ x, y = foo }`
    Record {
        typ: ArcType<Id>,
        types: Vec<PatternField<Id, Id>>,
        fields: Vec<PatternField<Id, SpannedPattern<'ast, Id>>>,
        implicit_import: Option<Spanned<Id, BytePos>>,
    },
    /// Tuple pattern, eg: `(x, y)`
    Tuple {
        typ: ArcType<Id>,
        elems: &'ast mut [SpannedPattern<'ast, Id>],
    },
    /// A literal pattern
    Literal(Literal),
    /// An invalid pattern
    Error,
}

impl<Id> Default for Pattern<'_, Id> {
    fn default() -> Self {
        Pattern::Error
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct Alternative<'ast, Id> {
    pub pattern: SpannedPattern<'ast, Id>,
    pub expr: SpannedExpr<'ast, Id>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Array<'ast, Id> {
    pub typ: ArcType<Id>,
    pub exprs: &'ast mut [SpannedExpr<'ast, Id>],
}

#[derive(Eq, PartialEq, Debug)]
pub struct Lambda<'ast, Id> {
    pub id: TypedIdent<Id>,
    pub args: Vec<Argument<SpannedIdent<Id>>>,
    pub body: &'ast mut SpannedExpr<'ast, Id>,
}

pub type SpannedExpr<'ast, Id> = Spanned<Expr<'ast, Id>, BytePos>;

pub type SpannedIdent<Id> = Spanned<TypedIdent<Id>, BytePos>;

pub type SpannedAlias<Id> = Spanned<AliasData<Id, AstType<Id>>, BytePos>;

pub type SpannedAstType<Id> = Spanned<Type<Id, AstType<Id>>, BytePos>;

#[derive(Eq, PartialEq, Debug)]
pub struct ExprField<Id, E> {
    pub metadata: Metadata,
    pub name: Spanned<Id, BytePos>,
    pub value: Option<E>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Do<'ast, Id> {
    pub id: Option<SpannedPattern<'ast, Id>>,
    pub bound: &'ast mut SpannedExpr<'ast, Id>,
    pub body: &'ast mut SpannedExpr<'ast, Id>,
    pub flat_map_id: Option<&'ast mut SpannedExpr<'ast, Id>>,
}

/// The representation of gluon's expression syntax
#[derive(Eq, PartialEq, Debug)]
pub enum Expr<'ast, Id> {
    /// Identifiers
    Ident(TypedIdent<Id>),
    /// Literal values
    Literal(Literal),
    /// Function application, eg. `f x`
    App {
        func: &'ast mut SpannedExpr<'ast, Id>,
        implicit_args: &'ast mut [SpannedExpr<'ast, Id>],
        args: &'ast mut [SpannedExpr<'ast, Id>],
    },
    /// Lambda abstraction, eg. `\x y -> x * y`
    Lambda(Lambda<'ast, Id>),
    /// If-then-else conditional
    IfElse(
        &'ast mut SpannedExpr<'ast, Id>,
        &'ast mut SpannedExpr<'ast, Id>,
        &'ast mut SpannedExpr<'ast, Id>,
    ),
    /// Pattern match expression
    Match(&'ast mut SpannedExpr<'ast, Id>, Vec<Alternative<'ast, Id>>),
    /// Infix operator expression eg. `f >> g`
    Infix {
        lhs: &'ast mut SpannedExpr<'ast, Id>,
        op: SpannedIdent<Id>,
        rhs: &'ast mut SpannedExpr<'ast, Id>,
        implicit_args: &'ast mut [SpannedExpr<'ast, Id>],
    },
    /// Record field projection, eg. `value.field`
    Projection(&'ast mut SpannedExpr<'ast, Id>, Id, ArcType<Id>),
    /// Array construction
    Array(Array<'ast, Id>),
    /// Record construction
    Record {
        typ: ArcType<Id>,
        types: Vec<ExprField<Id, ArcType<Id>>>,
        exprs: Vec<ExprField<Id, SpannedExpr<'ast, Id>>>,
        base: Option<&'ast mut SpannedExpr<'ast, Id>>,
    },
    /// Tuple construction
    Tuple {
        typ: ArcType<Id>,
        elems: &'ast mut [SpannedExpr<'ast, Id>],
    },
    /// Declare a series of value bindings
    LetBindings(ValueBindings<'ast, Id>, &'ast mut SpannedExpr<'ast, Id>),
    /// Declare a series of type aliases
    TypeBindings(Vec<TypeBinding<Id>>, &'ast mut SpannedExpr<'ast, Id>),
    /// A group of sequenced expressions
    Block(&'ast mut [SpannedExpr<'ast, Id>]),
    Do(Do<'ast, Id>),
    MacroExpansion {
        original: &'ast mut SpannedExpr<'ast, Id>,
        replacement: &'ast mut SpannedExpr<'ast, Id>,
    },
    Annotated(&'ast mut SpannedExpr<'ast, Id>, ArcType<Id>),
    /// An invalid expression
    Error(
        /// Provides a hint of what type the expression would have, if any
        Option<ArcType<Id>>,
    ),
}

impl<'ast, Id> Expr<'ast, Id> {
    pub fn rec_let_bindings(
        binds: Vec<ValueBinding<'ast, Id>>,
        expr: impl Into<&'ast mut SpannedExpr<'ast, Id>>,
    ) -> Self {
        Expr::LetBindings(ValueBindings::Recursive(binds), expr.into())
    }

    pub fn annotated<'a>(
        arena: ArenaRef<'ast, Id>,
        expr: SpannedExpr<'ast, Id>,
        typ: ArcType<Id>,
    ) -> SpannedExpr<'ast, Id>
    where
        Id: From<&'a str> + Clone,
    {
        pos::spanned(expr.span, Expr::Annotated(arena.alloc(expr), typ))
    }

    pub fn let_binding(
        bind: ValueBinding<'ast, Id>,
        expr: impl Into<&'ast mut SpannedExpr<'ast, Id>>,
    ) -> Self {
        Expr::LetBindings(ValueBindings::Plain(Box::new(bind)), expr.into())
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Expr::IfElse(..) => "IfElse",
            Expr::Infix { .. } => "Infix",
            Expr::LetBindings(..) => "LetBindings",
            Expr::App { .. } => "App",
            Expr::Projection(..) => "Projection",
            Expr::Match(..) => "Match",
            Expr::Array(..) => "Array",
            Expr::Record { .. } => "Record",
            Expr::Tuple { .. } => "Tuple",
            Expr::Block(..) => "Block",

            Expr::Do(Do { .. }) => "Do",

            Expr::Lambda(..) => "Lambda",
            Expr::TypeBindings(..) => "TypeBindings",
            Expr::Ident(..) => "Ident",
            Expr::MacroExpansion { .. } => "MacroExpansion",
            Expr::Literal(..) => "Literal",
            Expr::Annotated(..) => "Annotated",
            Expr::Error(..) => "Error",
        }
    }
}

impl<'ast, Id> Default for Expr<'ast, Id> {
    fn default() -> Self {
        Expr::Error(None)
    }
}

impl<'ast, Id> Expr<'ast, Id> {
    pub fn app(
        arena: ArenaRef<'ast, Id>,
        func: SpannedExpr<'ast, Id>,
        args: impl IntoIterator<Item = SpannedExpr<'ast, Id>>,
    ) -> Self {
        let args = arena.alloc_extend(args);
        if args.is_empty() {
            func.value
        } else {
            Expr::App {
                func: arena.alloc(func),
                implicit_args: &mut [],
                args,
            }
        }
    }

    // TODO Use impl Trait
    pub fn field_iter<'a>(
        &'a self,
    ) -> impl Iterator<
        Item = Either<&'a ExprField<Id, ArcType<Id>>, &'a ExprField<Id, SpannedExpr<'ast, Id>>>,
    > + 'a {
        let (types, exprs) = match *self {
            Expr::Record {
                ref types,
                ref exprs,
                ..
            } => (&types[..], &exprs[..]),
            _ => (&[][..], &[][..]),
        };
        types
            .iter()
            .map(Either::Left)
            .merge_by(exprs.iter().map(Either::Right), |x, y| {
                x.either(|l| l.name.span.start(), |r| r.name.span.start())
                    < y.either(|l| l.name.span.start(), |r| r.name.span.start())
            })
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub metadata: Metadata,
    pub name: Spanned<Id, BytePos>,
    pub alias: SpannedAlias<Id>,
    pub finalized_alias: Option<Alias<Id, ArcType<Id>>>,
}

impl<Id> TypeBinding<Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start(), self.alias.span.end())
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Argument<Id> {
    pub arg_type: ArgType,
    pub name: Id,
}

impl<Id> Argument<Id> {
    pub fn explicit(name: Id) -> Self {
        Argument {
            arg_type: ArgType::Explicit,
            name,
        }
    }

    pub fn implicit(name: Id) -> Self {
        Argument {
            arg_type: ArgType::Implicit,
            name,
        }
    }
}

#[derive(Eq, PartialEq, Debug)]
pub enum ValueBindings<'ast, Id> {
    Plain(Box<ValueBinding<'ast, Id>>),
    Recursive(Vec<ValueBinding<'ast, Id>>),
}

impl<'ast, Id> ValueBindings<'ast, Id> {
    pub fn is_recursive(&self) -> bool {
        match self {
            ValueBindings::Plain(ref bind) => !bind.args.is_empty(),
            ValueBindings::Recursive(_) => true,
        }
    }
}

impl<'ast, Id> Deref for ValueBindings<'ast, Id> {
    type Target = [ValueBinding<'ast, Id>];
    fn deref(&self) -> &Self::Target {
        match self {
            ValueBindings::Plain(bind) => slice::from_ref(&**bind),
            ValueBindings::Recursive(binds) => binds,
        }
    }
}

impl<'ast, Id> DerefMut for ValueBindings<'ast, Id> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ValueBindings::Plain(bind) => slice::from_mut(&mut **bind),
            ValueBindings::Recursive(binds) => binds,
        }
    }
}

impl<'a, 'ast, Id> IntoIterator for &'a ValueBindings<'ast, Id> {
    type IntoIter = slice::Iter<'a, ValueBinding<'ast, Id>>;
    type Item = &'a ValueBinding<'ast, Id>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, 'ast, Id> IntoIterator for &'a mut ValueBindings<'ast, Id> {
    type IntoIter = slice::IterMut<'a, ValueBinding<'ast, Id>>;
    type Item = &'a mut ValueBinding<'ast, Id>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct ValueBinding<'ast, Id> {
    pub metadata: Metadata,
    pub name: SpannedPattern<'ast, Id>,
    pub typ: Option<AstType<Id>>,
    pub resolved_type: ArcType<Id>,
    pub args: Vec<Argument<SpannedIdent<Id>>>,
    pub expr: SpannedExpr<'ast, Id>,
}

impl<T> Default for ValueBinding<'_, T>
where
    T: PartialEq,
{
    fn default() -> Self {
        ValueBinding {
            metadata: Default::default(),
            name: Default::default(),
            typ: Default::default(),
            resolved_type: Default::default(),
            args: Default::default(),
            expr: Default::default(),
        }
    }
}

impl<'ast, Id> ValueBinding<'ast, Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start(), self.expr.span.end())
    }
}

macro_rules! visitor {
    ($trait_name: ident, $unresolved_type: ident, $try_get_alias: ident, $($mut: tt)*) => {

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overridden the user will need to
/// call `walk_*` to continue traversing the tree.
pub trait $trait_name<'a, 'ast> {
    type Ident: 'a + 'ast;

    fn visit_expr(&mut self, e: &'a $($mut)* SpannedExpr<'ast, Self::Ident>) {
        walk_expr(self, e)
    }

    fn visit_pattern(&mut self, e: &'a $($mut)* SpannedPattern<'ast, Self::Ident>) {
        walk_pattern(self, &$($mut)* e.value);
    }

    fn visit_spanned_typed_ident(&mut self, id: &'a $($mut)* SpannedIdent<Self::Ident>) {
        self.visit_ident(&$($mut)* id.value)
    }

    fn visit_ident(&mut self, id: &'a $($mut)* TypedIdent<Self::Ident>) {
        self.visit_typ(&$($mut)* id.typ)
    }

    fn visit_alias(&mut self, alias: &'a $($mut)* SpannedAlias<Self::Ident>) {
        walk_alias(self, alias)
    }
    fn visit_spanned_ident(&mut self, _: &'a $($mut)* Spanned<Self::Ident, BytePos>) {}
    fn visit_typ(&mut self, _: &'a $($mut)* ArcType<Self::Ident>) {}
    fn visit_ast_type(&mut self, s: &'a $($mut)* SpannedAstType<Self::Ident>) {
        walk_ast_type(self, s);
    }
}

pub fn walk_alias<'a, 'ast, V>(
    v: &mut V,
    alias: &'a $($mut)* SpannedAlias<V::Ident>,
)
    where V: ?Sized + $trait_name<'a, 'ast>,
{
    v.visit_ast_type(&$($mut)* alias.value.$unresolved_type()._typ.typ);
}

pub fn walk_expr<'a, 'ast, V>(v: &mut V, e: &'a $($mut)* SpannedExpr<'ast, V::Ident>)
    where V: ?Sized + $trait_name<'a, 'ast>,
{
    match e.value {
        Expr::IfElse(ref $($mut)* pred, ref $($mut)* if_true, ref $($mut)* if_false) => {
            v.visit_expr(pred);
            v.visit_expr(if_true);
            v.visit_expr(if_false);
        }
        Expr::Infix {
            ref $($mut)* lhs,
            ref $($mut)* op,
            ref $($mut)* rhs,
            ref $($mut)* implicit_args,
        } => {
            v.visit_expr(lhs);
            v.visit_spanned_typed_ident(op);
            v.visit_expr(rhs);
            for arg in &$($mut)* **implicit_args {
                v.visit_expr(arg);
            }
        }
        Expr::LetBindings(ref $($mut)* bindings, ref $($mut)* body) => {
            for bind in bindings {
                v.visit_pattern(&$($mut)* bind.name);
                for arg in &$($mut)* bind.args {
                    v.visit_spanned_typed_ident(&$($mut)* arg.name);
                }
                v.visit_typ(&$($mut)* bind.resolved_type);
                v.visit_expr(&$($mut)* bind.expr);
                if let Some(ref $($mut)* ast_type) = bind.typ {
                    v.visit_ast_type(&$($mut)* ast_type._typ.typ)
                }
            }
            v.visit_expr(body);
        }
        Expr::App {
            ref $($mut)* func,
            ref $($mut)* implicit_args,
            ref $($mut)* args,
        } => {
            v.visit_expr(func);
            for arg in &$($mut)* **implicit_args {
                v.visit_expr(arg);
            }
            for arg in & $($mut)* **args {
                v.visit_expr(arg);
            }
        }
        Expr::Projection(ref $($mut)* expr, _, ref $($mut)* typ) => {
            v.visit_typ(typ);
            v.visit_expr(expr);
        }
        Expr::Match(ref $($mut)* expr, ref $($mut)* alts) => {
            v.visit_expr(expr);
            for alt in alts {
                v.visit_pattern(&$($mut)* alt.pattern);
                v.visit_expr(&$($mut)* alt.expr);
            }
        }
        Expr::Array(ref $($mut)* a) => {
            v.visit_typ(&$($mut)* a.typ);
            for expr in &$($mut)* *a.exprs {
                v.visit_expr(expr);
            }
        }
        Expr::Record {
            ref $($mut)* typ,
            ref $($mut)* types,
            ref $($mut)* exprs,
            ref $($mut)* base,
            ..
        } => {
            v.visit_typ(typ);
            for typ in types {
                v.visit_spanned_ident(&$($mut)* typ.name);
            }
            for field in &$($mut)* **exprs {
                v.visit_spanned_ident(&$($mut)* field.name);
                if let Some(ref $($mut)* expr) = field.value {
                    v.visit_expr(expr);
                }
            }
            if let Some(ref $($mut)* base) = *base {
                v.visit_expr(base);
            }
        }
        Expr::Tuple {
            ref $($mut)* typ,
            ref $($mut)* elems,
        } => {
            v.visit_typ(typ);
            for expr in &$($mut)* **elems {
                v.visit_expr(expr);
            }
        }
        Expr::Block(ref $($mut)* exprs) => for expr in &$($mut)* **exprs {
            v.visit_expr(expr);
        },

        Expr::Do(Do {
            ref $($mut)* id,
            ref $($mut)* bound,
            ref $($mut)* body,
            ref $($mut)* flat_map_id,
        }) => {
            if let Some(id) = id {
                v.visit_pattern(id);
            }
            v.visit_expr(bound);
            v.visit_expr(body);
            if let Some(ref $($mut)* flat_map_id) = *flat_map_id {
                v.visit_expr(flat_map_id);
            }
        }

        Expr::Lambda(ref $($mut)* lambda) => {
            v.visit_ident(&$($mut)* lambda.id);
            for arg in &$($mut)* lambda.args {
                v.visit_spanned_typed_ident(&$($mut)* arg.name);
            }
            v.visit_expr(&$($mut)* lambda.body);
        }
        Expr::TypeBindings(ref $($mut)* bindings, ref $($mut)* expr) => {
            for binding in bindings {
                v.visit_spanned_ident(&$($mut)* binding.name);
                v.visit_alias(&$($mut)* binding.alias);
            }
            v.visit_expr(expr)
        }
        Expr::Ident(ref $($mut)* id) => v.visit_ident(id),
        Expr::MacroExpansion {
            ref $($mut)* replacement,
            ..
        } => v.visit_expr(replacement),
        Expr::Annotated(ref $($mut)* expr, ref $($mut)* typ) => {
            v.visit_typ(typ);
            v.visit_expr(expr);
        }
        Expr::Literal(..) | Expr::Error(..) => (),
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_pattern<'a, 'ast,V: ?Sized + $trait_name<'a, 'ast>>(v: &mut V, p: &'a $($mut)* Pattern<'ast, V::Ident>) {
    match *p {
        Pattern::As(ref $($mut)* id, ref $($mut)* pat) => {
            v.visit_spanned_ident(id);
            v.visit_pattern(pat);
        }
        Pattern::Constructor(ref $($mut)* id, ref $($mut)* args) => {
            v.visit_ident(id);
            for arg in &$($mut)* **args {
                v.visit_pattern(arg);
            }
        }
        Pattern::Record {
            ref $($mut)* typ,
            ref $($mut)* fields,
            ..
        } => {
            v.visit_typ(typ);
            for field in fields {
                v.visit_spanned_ident(&$($mut)* field.name);
                if let Some(ref $($mut)* pattern) = field.value {
                    v.visit_pattern(pattern);
                }
            }
        }
        Pattern::Tuple {
            ref $($mut)* typ,
            ref $($mut)* elems,
        } => {
            v.visit_typ(typ);
            for elem in &$($mut)* **elems {
                v.visit_pattern(elem);
            }
        }
        Pattern::Ident(ref $($mut)* id) => v.visit_ident(id),
        Pattern::Literal(_) | Pattern::Error => (),
    }
}

pub fn walk_ast_type<'a, 'ast, V: ?Sized + $trait_name<'a, 'ast>>(
    v: &mut V,
    s: &'a $($mut)* SpannedAstType<V::Ident>,
) {
    match s.value {
        Type::Hole | Type::Opaque | Type::Error | Type::Builtin(_) => (),
        Type::Forall(_, ref $($mut)* ast_type) => {
            v.visit_ast_type(&$($mut)* ast_type._typ.typ);
        }
        Type::Function(_, ref $($mut)* arg, ref $($mut)* ret) => {
            v.visit_ast_type(&$($mut)* arg._typ.typ);
            v.visit_ast_type(&$($mut)* ret._typ.typ);
        }
        Type::App(ref $($mut)* ast_type, ref $($mut)* ast_types) => {
            for ast_type in ast_types {
                v.visit_ast_type(&$($mut)* ast_type._typ.typ);
            }
            v.visit_ast_type(&$($mut)* ast_type._typ.typ)
        }
        Type::Record(ref $($mut)* ast_type) => v.visit_ast_type(&$($mut)* ast_type._typ.typ),
        Type::Variant(ref $($mut)* ast_type) => v.visit_ast_type(&$($mut)* ast_type._typ.typ),
        Type::Effect(ref $($mut)* ast_type) => v.visit_ast_type(&$($mut)* ast_type._typ.typ),
        Type::EmptyRow => (),
        Type::ExtendRow {
            ref $($mut)* fields,
            ref $($mut)* rest,
        } => {
            for field in fields {
                v.visit_ast_type(&$($mut)* field.typ._typ.typ);
            }
            v.visit_ast_type(&$($mut)* rest._typ.typ);
        }
        Type::ExtendTypeRow {
            ref $($mut)* types,
            ref $($mut)* rest,
        } => {
            for field in types {
                if let Some(alias) = field.typ.$try_get_alias() {
                    v.visit_ast_type(&$($mut)* alias.$unresolved_type()._typ.typ);
                }
            }
            v.visit_ast_type(&$($mut)* rest._typ.typ);
        }
        Type::Alias(ref $($mut)* alias) => {
            if let Some(alias) = alias.$try_get_alias() {
                v.visit_ast_type(&$($mut)* alias.$unresolved_type()._typ.typ);
            }
        }
        Type::Ident(_) | Type::Projection(_) | Type::Variable(_) | Type::Generic(_) | Type::Skolem(_) => (),
    }
}
    }
}

mod mut_ {
    use super::*;
    visitor!(MutVisitor, unresolved_type_mut, try_get_alias_mut, mut);
}
pub use self::mut_::{
    walk_alias as walk_mut_alias, walk_ast_type as walk_mut_ast_type, walk_expr as walk_mut_expr,
    walk_pattern as walk_mut_pattern, MutVisitor,
};
mod ref_ {
    use super::*;
    visitor!(Visitor, unresolved_type, try_get_alias,);
}
pub use self::ref_::{walk_alias, walk_ast_type, walk_expr, walk_pattern, Visitor};

/// Trait which abstracts over things that have a type.
/// It is not guaranteed that the correct type is returned until after typechecking
pub trait Typed {
    type Ident;

    fn env_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> ArcType<Self::Ident> {
        self.try_type_of(env).unwrap()
    }

    fn try_type_of(
        &self,
        env: &dyn TypeEnv<Type = ArcType>,
    ) -> Result<ArcType<Self::Ident>, String>;
}

impl<Id: Clone> Typed for TypedIdent<Id> {
    type Ident = Id;

    fn try_type_of(&self, _: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType<Id>, String> {
        Ok(self.typ.clone())
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

impl Typed for Expr<'_, Symbol> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType, String> {
        match *self {
            Expr::Ident(ref id) => Ok(id.typ.clone()),
            Expr::Tuple { ref elems, .. } if elems.len() == 1 => elems[0].try_type_of(env),
            Expr::Projection(_, _, ref typ)
            | Expr::Record { ref typ, .. }
            | Expr::Tuple { ref typ, .. } => Ok(typ.clone()),
            Expr::Literal(ref lit) => lit.try_type_of(env),
            Expr::IfElse(_, ref arm, _) => arm.try_type_of(env),
            Expr::Infix { ref op, .. } => get_return_type(env, &op.value.typ, 2),
            Expr::LetBindings(_, ref expr)
            | Expr::TypeBindings(_, ref expr)
            | Expr::Do(Do { body: ref expr, .. }) => expr.try_type_of(env),
            Expr::App {
                ref func, ref args, ..
            } => get_return_type(env, &func.try_type_of(env)?, args.len()),
            Expr::Match(_, ref alts) => alts[0].expr.try_type_of(env),
            Expr::Array(ref array) => Ok(array.typ.clone()),
            Expr::Lambda(ref lambda) => Ok(lambda.id.typ.clone()),
            Expr::Block(ref exprs) => exprs.last().expect("Expr in block").try_type_of(env),
            Expr::MacroExpansion {
                ref replacement, ..
            } => replacement.try_type_of(env),
            Expr::Annotated(_, ref typ) => Ok(typ.clone()),
            Expr::Error(ref typ) => Ok(typ.clone().unwrap_or_else(Type::hole)),
        }
    }
}

impl<T: Typed> Typed for Spanned<T, BytePos> {
    type Ident = T::Ident;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType<T::Ident>, String> {
        self.value.try_type_of(env)
    }
}

impl Typed for Pattern<'_, Symbol> {
    type Ident = Symbol;
    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType, String> {
        // Identifier patterns might be a function so use the identifier's type instead
        match *self {
            Pattern::As(_, ref pat) => pat.try_type_of(env),
            Pattern::Ident(ref id) => Ok(id.typ.clone()),
            Pattern::Record { ref typ, .. } => Ok(typ.clone()),
            Pattern::Tuple { ref typ, .. } => Ok(typ.clone()),
            Pattern::Constructor(ref id, ref args) => get_return_type(env, &id.typ, args.len()),
            Pattern::Error => Ok(Type::hole()),
            Pattern::Literal(ref l) => l.try_type_of(env),
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
    let function_type = remove_aliases_cow(env, &mut NullInterner, alias_type);

    let ret = function_type
        .remove_forall_and_implicit_args()
        .as_function()
        .map(|t| Cow::Borrowed(t.1))
        .ok_or_else(|| format!("Unexpected type {} is not a function", alias_type))?;

    get_return_type(env, &ret, arg_count - 1)
}

pub fn is_operator_char(c: char) -> bool {
    (c as u32) < 128 && is_operator_byte(c as u8)
}

pub fn is_operator_byte(c: u8) -> bool {
    macro_rules! match_token {
        ($($x: pat),*) => {
            match c {
                $($x)|* => true,
                _ => false,
            }
        }
    }
    match_token! {
        b'!',
        b'#',
        b'$',
        b'%',
        b'&',
        b'*',
        b'+',
        b'-',
        b'.',
        b'/',
        b'<',
        b'=',
        b'>',
        b'?',
        b'@',
        b'\\',
        b'^',
        b'|',
        b'~',
        b':'
    }
}

pub fn is_constructor(s: &str) -> bool {
    s.rsplit('.')
        .next()
        .unwrap()
        .starts_with(char::is_uppercase)
}

pub fn expr_to_path(expr: &SpannedExpr<Symbol>, path: &mut String) -> Result<(), &'static str> {
    match expr.value {
        Expr::Ident(ref id) => {
            path.push_str(id.name.declared_name());
            Ok(())
        }
        Expr::Projection(ref expr, ref id, _) => {
            expr_to_path(expr, path)?;
            path.push('.');
            path.push_str(id.declared_name());
            Ok(())
        }
        _ => Err("Expected a string literal or path to import"),
    }
}

use std::mem;
use std::sync::Arc;

pub type ArenaRef<'ast, Id> = &'ast Arena<'ast, Id>;

#[derive(Clone)]
pub struct Arena<'ast, Id>(Arc<ArenaInner<'ast, Id>>);
struct ArenaInner<'ast, Id> {
    exprs: typed_arena::Arena<SpannedExpr<'ast, Id>>,
    patterns: typed_arena::Arena<SpannedPattern<'ast, Id>>,
}

impl<'ast, Id> Arena<'ast, Id> {
    pub unsafe fn new(_: &'ast InvariantLifetime<'ast>) -> Self {
        Arena(Arc::new(ArenaInner {
            exprs: typed_arena::Arena::new(),
            patterns: typed_arena::Arena::new(),
        }))
    }

    pub fn alloc<T>(&'ast self, value: T) -> &'ast mut T
    where
        T: AstAlloc<'ast, Id>,
    {
        value.alloc(self)
    }

    pub fn alloc_extend<T>(&'ast self, iter: impl IntoIterator<Item = T>) -> &'ast mut [T]
    where
        T: AstAlloc<'ast, Id>,
    {
        T::alloc_extend(iter, self)
    }
}

pub trait AstAlloc<'ast, Id>: Sized {
    fn alloc(self, arena: &'ast Arena<'ast, Id>) -> &'ast mut Self;
    fn alloc_extend(
        iter: impl IntoIterator<Item = Self>,
        arena: &'ast Arena<'ast, Id>,
    ) -> &'ast mut [Self];
}

impl<'ast, Id> AstAlloc<'ast, Id> for SpannedExpr<'ast, Id> {
    fn alloc(self, arena: &'ast Arena<'ast, Id>) -> &'ast mut Self {
        arena.0.exprs.alloc(self)
    }

    fn alloc_extend(
        iter: impl IntoIterator<Item = Self>,
        arena: &'ast Arena<'ast, Id>,
    ) -> &'ast mut [Self] {
        arena.0.exprs.alloc_extend(iter)
    }
}

impl<'ast, Id> AstAlloc<'ast, Id> for SpannedPattern<'ast, Id> {
    fn alloc(self, arena: &'ast Arena<'ast, Id>) -> &'ast mut Self {
        arena.0.patterns.alloc(self)
    }

    fn alloc_extend(
        iter: impl IntoIterator<Item = Self>,
        arena: &'ast Arena<'ast, Id>,
    ) -> &'ast mut [Self] {
        arena.0.patterns.alloc_extend(iter)
    }
}

pub struct RootSpannedExpr<Id: 'static> {
    // Only used to keep `expr` alive
    #[allow(dead_code)]
    arena: Arena<'static, Id>,
    expr: *mut SpannedExpr<'static, Id>,
}

impl<Id: PartialEq> PartialEq for RootSpannedExpr<Id> {
    fn eq(&self, other: &Self) -> bool {
        self.expr() == other.expr()
    }
}

impl<Id: fmt::Debug> fmt::Debug for RootSpannedExpr<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.expr().fmt(f)
    }
}

impl<Id> RootSpannedExpr<Id> {
    pub fn new<'ast>(arena: Arena<'ast, Id>, expr: &'ast mut SpannedExpr<'ast, Id>) -> Self {
        // SAFETY Arena<'ast> can only be constructed with an invariant lifetime which means that
        // `expr` must come from that arena. This locks the lifetime of `expr` to `arena` so that
        // the expression won't be dropped before the arena is
        unsafe {
            Self {
                arena: mem::transmute::<Arena<Id>, Arena<Id>>(arena),
                expr: mem::transmute::<*mut SpannedExpr<Id>, *mut SpannedExpr<Id>>(expr),
            }
        }
    }

    pub fn with_arena<R>(
        &mut self,
        f: impl for<'ast> FnOnce(&'ast Arena<'ast, Id>, &'ast mut SpannedExpr<'ast, Id>) -> R,
    ) -> R {
        unsafe {
            f(
                mem::transmute::<&Arena<Id>, &Arena<Id>>(&self.arena),
                &mut *self.expr,
            )
        }
    }

    pub fn expr(&self) -> &SpannedExpr<'_, Id> {
        unsafe { mem::transmute::<&SpannedExpr<Id>, &SpannedExpr<Id>>(&*self.expr) }
    }

    pub fn expr_mut(&mut self) -> &mut SpannedExpr<'_, Id> {
        unsafe { mem::transmute::<&mut SpannedExpr<Id>, &mut SpannedExpr<Id>>(&mut *self.expr) }
    }
}

#[doc(hidden)]
#[derive(Default)]
pub struct InvariantLifetime<'a>(std::marker::PhantomData<fn(&'a ()) -> &'a ()>);

// Copied from the compact_arena crate
#[macro_export]
macro_rules! mk_ast_arena {
    ($name: ident) => {
        let tag = $crate::ast::InvariantLifetime::default();
        let $name = unsafe { $crate::ast::Arena::new(&tag) };
        let _guard;
        // this doesn't make it to MIR, but ensures that borrowck will not
        // unify the lifetimes of two macro calls by binding the lifetime to
        // drop scope
        if false {
            struct Guard<'tag>(&'tag $crate::ast::InvariantLifetime<'tag>);
            impl<'tag> ::core::ops::Drop for Guard<'tag> {
                fn drop(&mut self) {}
            }
            _guard = Guard(&tag);
        }
    };
}
