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

use metadata::{Comment, Metadata};
use ordered_float::NotNan;
use pos::{self, BytePos, HasSpan, Span, Spanned};
use resolve::remove_aliases_cow;
use symbol::Symbol;
use types::{self, Alias, AliasData, ArcType, ArgType, Type, TypeEnv};

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
    comment: Option<Comment>,
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
            _typ: Box::new(InnerAstType { comment: None, typ }),
        }
    }
}

impl<Id> From<Type<Id, AstType<Id>>> for AstType<Id> {
    fn from(typ: Type<Id, AstType<Id>>) -> Self {
        Self::from(pos::spanned2(0.into(), 0.into(), typ))
    }
}

impl<Id> HasSpan for AstType<Id> {
    fn span(&self) -> Span<BytePos> {
        self._typ.typ.span
    }
}

pub trait Commented {
    fn comment(&self) -> Option<&Comment>;
}

impl<Id> Commented for AstType<Id> {
    fn comment(&self) -> Option<&Comment> {
        self._typ.comment.as_ref()
    }
}

impl<Id> AstType<Id> {
    pub fn with_comment<T>(comment: T, typ: Spanned<Type<Id, AstType<Id>>, BytePos>) -> Self
    where
        T: Into<Option<Comment>>,
    {
        AstType {
            _typ: Box::new(InnerAstType {
                comment: comment.into(),
                typ,
            }),
        }
    }

    pub fn set_comment<T>(&mut self, comment: T)
    where
        T: Into<Option<Comment>>,
    {
        self._typ.comment = comment.into();
    }

    pub fn into_inner(self) -> Type<Id, Self> {
        self._typ.typ.value
    }

    pub fn remove_single_forall(&mut self) -> &mut AstType<Id> {
        match self._typ.typ.value {
            Type::Forall(_, ref mut typ, _) => typ,
            _ => self,
        }
    }
}

impl<Id> AsMut<SpannedAstType<Id>> for AstType<Id> {
    fn as_mut(&mut self) -> &mut SpannedAstType<Id> {
        &mut self._typ.typ
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypedIdent<Id = Symbol> {
    pub typ: ArcType<Id>,
    pub name: Id,
}

impl<Id> TypedIdent<Id> {
    pub fn new(name: Id) -> TypedIdent<Id> {
        TypedIdent {
            typ: Type::hole(),
            name,
        }
    }
}

impl<Id> AsRef<str> for TypedIdent<Id>
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
pub type SpannedPattern<Id> = Spanned<Pattern<Id>, BytePos>;

#[derive(Clone, PartialEq, Debug)]
pub struct PatternField<Id, P> {
    pub name: Spanned<Id, BytePos>,
    pub value: Option<P>,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id> {
    /// An as-pattern, eg. `option @ { monoid, functor }`
    As(Spanned<Id, BytePos>, Box<SpannedPattern<Id>>),
    /// Constructor pattern, eg. `Cons x xs`
    Constructor(TypedIdent<Id>, Vec<SpannedPattern<Id>>),
    /// Ident pattern, eg: `x`
    Ident(TypedIdent<Id>),
    /// Record pattern, eg. `{ x, y = foo }`
    Record {
        typ: ArcType<Id>,
        types: Vec<PatternField<Id, Id>>,
        fields: Vec<PatternField<Id, SpannedPattern<Id>>>,
        implicit_import: Option<Spanned<Id, BytePos>>,
    },
    /// Tuple pattern, eg: `(x, y)`
    Tuple {
        typ: ArcType<Id>,
        elems: Vec<SpannedPattern<Id>>,
    },
    /// A literal pattern
    Literal(Literal),
    /// An invalid pattern
    Error,
}

impl<Id> Default for Pattern<Id> {
    fn default() -> Self {
        Pattern::Error
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id> {
    pub pattern: SpannedPattern<Id>,
    pub expr: SpannedExpr<Id>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Array<Id> {
    pub typ: ArcType<Id>,
    pub exprs: Vec<SpannedExpr<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Lambda<Id> {
    pub id: TypedIdent<Id>,
    pub args: Vec<Argument<SpannedIdent<Id>>>,
    pub body: Box<SpannedExpr<Id>>,
}

pub type SpannedExpr<Id> = Spanned<Expr<Id>, BytePos>;

pub type SpannedIdent<Id> = Spanned<TypedIdent<Id>, BytePos>;

pub type SpannedAlias<Id> = Spanned<AliasData<Id, AstType<Id>>, BytePos>;

pub type SpannedAstType<Id> = Spanned<Type<Id, AstType<Id>>, BytePos>;

#[derive(Clone, PartialEq, Debug)]
pub struct ExprField<Id, E> {
    pub metadata: Metadata,
    pub name: Spanned<Id, BytePos>,
    pub value: Option<E>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Do<Id> {
    pub id: SpannedIdent<Id>,
    pub bound: Box<SpannedExpr<Id>>,
    pub body: Box<SpannedExpr<Id>>,
    pub flat_map_id: Option<Box<SpannedExpr<Id>>>,
}

/// The representation of gluon's expression syntax
#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id> {
    /// Identifiers
    Ident(TypedIdent<Id>),
    /// Literal values
    Literal(Literal),
    /// Function application, eg. `f x`
    App {
        func: Box<SpannedExpr<Id>>,
        implicit_args: Vec<SpannedExpr<Id>>,
        args: Vec<SpannedExpr<Id>>,
    },
    /// Lambda abstraction, eg. `\x y -> x * y`
    Lambda(Lambda<Id>),
    /// If-then-else conditional
    IfElse(
        Box<SpannedExpr<Id>>,
        Box<SpannedExpr<Id>>,
        Box<SpannedExpr<Id>>,
    ),
    /// Pattern match expression
    Match(Box<SpannedExpr<Id>>, Vec<Alternative<Id>>),
    /// Infix operator expression eg. `f >> g`
    Infix {
        lhs: Box<SpannedExpr<Id>>,
        op: SpannedIdent<Id>,
        rhs: Box<SpannedExpr<Id>>,
        implicit_args: Vec<SpannedExpr<Id>>,
    },
    /// Record field projection, eg. `value.field`
    Projection(Box<SpannedExpr<Id>>, Id, ArcType<Id>),
    /// Array construction
    Array(Array<Id>),
    /// Record construction
    Record {
        typ: ArcType<Id>,
        types: Vec<ExprField<Id, ArcType<Id>>>,
        exprs: Vec<ExprField<Id, SpannedExpr<Id>>>,
        base: Option<Box<SpannedExpr<Id>>>,
    },
    /// Tuple construction
    Tuple {
        typ: ArcType<Id>,
        elems: Vec<SpannedExpr<Id>>,
    },
    /// Declare a series of value bindings
    LetBindings(ValueBindings<Id>, Box<SpannedExpr<Id>>),
    /// Declare a series of type aliases
    TypeBindings(Vec<TypeBinding<Id>>, Box<SpannedExpr<Id>>),
    /// A group of sequenced expressions
    Block(Vec<SpannedExpr<Id>>),
    Do(Do<Id>),
    MacroExpansion {
        original: Box<SpannedExpr<Id>>,
        replacement: Box<SpannedExpr<Id>>,
    },
    Annotated(Box<SpannedExpr<Id>>, ArcType<Id>),
    /// An invalid expression
    Error(
        /// Provides a hint of what type the expression would have, if any
        Option<ArcType<Id>>,
    ),
}

impl<Id> Expr<Id> {
    pub fn rec_let_bindings(
        binds: Vec<ValueBinding<Id>>,
        expr: impl Into<Box<SpannedExpr<Id>>>,
    ) -> Self {
        Expr::LetBindings(ValueBindings::Recursive(binds), expr.into())
    }

    pub fn annotated<'a>(expr: SpannedExpr<Id>, typ: ArcType<Id>) -> SpannedExpr<Id>
    where
        Id: From<&'a str> + Clone,
    {
        pos::spanned(expr.span, Expr::Annotated(expr.into(), typ))
    }

    pub fn let_binding(bind: ValueBinding<Id>, expr: impl Into<Box<SpannedExpr<Id>>>) -> Self {
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

impl<Id> Default for Expr<Id> {
    fn default() -> Self {
        Expr::Error(None)
    }
}

impl<Id> Expr<Id> {
    // TODO Use impl Trait
    pub fn field_iter<'a>(
        &'a self,
    ) -> impl Iterator<
        Item = Either<&'a ExprField<Id, ArcType<Id>>, &'a ExprField<Id, SpannedExpr<Id>>>,
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

#[derive(Clone, PartialEq, Debug)]
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

#[derive(Clone, Eq, PartialEq, Debug)]
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

#[derive(Clone, PartialEq, Debug)]
pub enum ValueBindings<Id> {
    Plain(Box<ValueBinding<Id>>),
    Recursive(Vec<ValueBinding<Id>>),
}

impl<Id> ValueBindings<Id> {
    pub fn is_recursive(&self) -> bool {
        match self {
            ValueBindings::Plain(ref bind) => !bind.args.is_empty(),
            ValueBindings::Recursive(_) => true,
        }
    }
}

impl<Id> Deref for ValueBindings<Id> {
    type Target = [ValueBinding<Id>];
    fn deref(&self) -> &Self::Target {
        match self {
            ValueBindings::Plain(bind) => slice::from_ref(&**bind),
            ValueBindings::Recursive(binds) => binds,
        }
    }
}

impl<Id> DerefMut for ValueBindings<Id> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ValueBindings::Plain(bind) => slice::from_mut(&mut **bind),
            ValueBindings::Recursive(binds) => binds,
        }
    }
}

impl<'a, Id> IntoIterator for &'a ValueBindings<Id> {
    type IntoIter = slice::Iter<'a, ValueBinding<Id>>;
    type Item = &'a ValueBinding<Id>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, Id> IntoIterator for &'a mut ValueBindings<Id> {
    type IntoIter = slice::IterMut<'a, ValueBinding<Id>>;
    type Item = &'a mut ValueBinding<Id>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueBinding<Id> {
    pub metadata: Metadata,
    pub name: SpannedPattern<Id>,
    pub typ: Option<AstType<Id>>,
    pub resolved_type: ArcType<Id>,
    pub args: Vec<Argument<SpannedIdent<Id>>>,
    pub expr: SpannedExpr<Id>,
}

impl<T> Default for ValueBinding<T> {
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

impl<Id> ValueBinding<Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start(), self.expr.span.end())
    }
}

macro_rules! visitor {
    ($trait_name: ident, $unresolved_type: ident, $try_get_alias: ident, $($mut: tt)*) => {

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overridden the user will need to
/// call `walk_*` to continue traversing the tree.
pub trait $trait_name<'a> {
    type Ident: 'a;

    fn visit_expr(&mut self, e: &'a $($mut)* SpannedExpr<Self::Ident>) {
        walk_expr(self, e);
    }

    fn visit_pattern(&mut self, e: &'a $($mut)* SpannedPattern<Self::Ident>) {
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

pub fn walk_alias<'a, V: ?Sized + $trait_name<'a>>(
    v: &mut V,
    alias: &'a $($mut)* SpannedAlias<V::Ident>,
) {
    v.visit_ast_type(&$($mut)* alias.value.$unresolved_type()._typ.typ);
}

pub fn walk_expr<'a, V: ?Sized + $trait_name<'a>>(v: &mut V, e: &'a $($mut)* SpannedExpr<V::Ident>) {
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
            for arg in implicit_args {
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
            for arg in implicit_args {
                v.visit_expr(arg);
            }
            for arg in args {
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
            for expr in &$($mut)* a.exprs {
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
            for field in exprs {
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
            for expr in elems {
                v.visit_expr(expr);
            }
        }
        Expr::Block(ref $($mut)* exprs) => for expr in exprs {
            v.visit_expr(expr);
        },

        Expr::Do(Do {
            ref $($mut)* id,
            ref $($mut)* bound,
            ref $($mut)* body,
            ref $($mut)* flat_map_id,
        }) => {
            v.visit_spanned_typed_ident(id);
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
pub fn walk_pattern<'a, V: ?Sized + $trait_name<'a>>(v: &mut V, p: &'a $($mut)* Pattern<V::Ident>) {
    match *p {
        Pattern::As(ref $($mut)* id, ref $($mut)* pat) => {
            v.visit_spanned_ident(id);
            v.visit_pattern(pat);
        }
        Pattern::Constructor(ref $($mut)* id, ref $($mut)* args) => {
            v.visit_ident(id);
            for arg in args {
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
            for elem in elems {
                v.visit_pattern(elem);
            }
        }
        Pattern::Ident(ref $($mut)* id) => v.visit_ident(id),
        Pattern::Literal(_) | Pattern::Error => (),
    }
}

pub fn walk_ast_type<'a, V: ?Sized + $trait_name<'a>>(
    v: &mut V,
    s: &'a $($mut)* SpannedAstType<V::Ident>,
) {
    match s.value {
        Type::Hole | Type::Opaque | Type::Error | Type::Builtin(_) => (),
        Type::Forall(_, ref $($mut)* ast_type, ref $($mut)* ast_types) => {
            v.visit_ast_type(&$($mut)* ast_type._typ.typ);
            if let Some(ref $($mut)* ast_types) = *ast_types {
                for ast_type in ast_types {
                    v.visit_ast_type(&$($mut)* ast_type._typ.typ);
                }
            }
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
            ref $($mut)* types,
            ref $($mut)* fields,
            ref $($mut)* rest,
        } => {
            for field in types {
                if let Some(alias) = field.typ.$try_get_alias() {
                    v.visit_ast_type(&$($mut)* alias.$unresolved_type()._typ.typ);
                }
            }
            for field in fields {
                v.visit_ast_type(&$($mut)* field.typ._typ.typ);
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

    fn env_type_of(&self, env: &TypeEnv) -> ArcType<Self::Ident> {
        self.try_type_of(env).unwrap()
    }

    fn try_type_of(&self, env: &TypeEnv) -> Result<ArcType<Self::Ident>, String>;
}

impl<Id: Clone> Typed for TypedIdent<Id> {
    type Ident = Id;

    fn try_type_of(&self, _: &TypeEnv) -> Result<ArcType<Id>, String> {
        Ok(self.typ.clone())
    }
}

impl Typed for Literal {
    type Ident = Symbol;

    fn try_type_of(&self, _: &TypeEnv) -> Result<ArcType, String> {
        Ok(match *self {
            Literal::Int(_) => Type::int(),
            Literal::Float(_) => Type::float(),
            Literal::Byte(_) => Type::byte(),
            Literal::String(_) => Type::string(),
            Literal::Char(_) => Type::char(),
        })
    }
}

impl Typed for Expr<Symbol> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &TypeEnv) -> Result<ArcType, String> {
        match *self {
            Expr::Ident(ref id) => Ok(id.typ.clone()),
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

    fn try_type_of(&self, env: &TypeEnv) -> Result<ArcType<T::Ident>, String> {
        self.value.try_type_of(env)
    }
}

impl Typed for Pattern<Symbol> {
    type Ident = Symbol;
    fn try_type_of(&self, env: &TypeEnv) -> Result<ArcType, String> {
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
    env: &TypeEnv,
    alias_type: &ArcType,
    arg_count: usize,
) -> Result<ArcType, String> {
    if arg_count == 0 || **alias_type == Type::Hole {
        return Ok(alias_type.clone());
    }
    let function_type = remove_aliases_cow(env, alias_type);

    let ret = function_type
        .remove_forall_and_implicit_args()
        .as_function()
        .map(|t| Cow::Borrowed(t.1))
        .ok_or_else(|| format!("Unexpected type {} is not a function", alias_type))?;

    get_return_type(env, &ret, arg_count - 1)
}

pub fn is_operator_char(c: char) -> bool {
    macro_rules! match_token {
        ($($x: pat),*) => {
            match c {
                $($x)|* => true,
                _ => false,
            }
        }
    }
    match_token! {
        '!',
        '#',
        '$',
        '%',
        '&',
        '*',
        '+',
        '-',
        '.',
        '/',
        '<',
        '=',
        '>',
        '?',
        '@',
        '\\',
        '^',
        '|',
        '~',
        ':'
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
