//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)
use std::{
    borrow::Cow,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    slice,
};

use {either::Either, itertools::Itertools, ordered_float::NotNan};

use gluon_codegen::AstClone;

#[cfg(feature = "serde")]
use crate::{
    serde::de::DeserializeState,
    serialization::{SeSeed, Seed},
};

use crate::{
    kind::ArcKind,
    metadata::{BaseMetadata, Comment, Metadata},
    pos::{self, BytePos, HasSpan, Span, Spanned},
    resolve::remove_aliases_cow,
    symbol::Symbol,
    types::{
        self, Alias, AliasData, ArcType, ArgType, AsId, Field, Generic, NullInterner, Type,
        TypeEnv, TypeExt, TypePtr,
    },
};

pub type Sp<T> = Spanned<T, BytePos>;

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

#[derive(Eq, PartialEq, AstClone)]
pub struct InnerAstType<'ast, Id> {
    metadata: BaseMetadata<'ast>,
    typ: Spanned<Type<Id, AstType<'ast, Id>>, BytePos>,
}

#[derive(Eq, PartialEq, AstClone)]
pub struct AstType<'ast, Id> {
    _typ: &'ast mut InnerAstType<'ast, Id>,
}

// Workaround https://github.com/rust-lang/rust/issues/70083
unsafe impl<'ast, Id> Send for AstType<'ast, Id> where Id: Send {}
unsafe impl<'ast, Id> Sync for AstType<'ast, Id> where Id: Sync {}
impl<'ast, Id> std::panic::RefUnwindSafe for AstType<'ast, Id> where Id: std::panic::RefUnwindSafe {}

impl<'ast, Id> Deref for AstType<'ast, Id> {
    type Target = Type<Id, AstType<'ast, Id>>;

    fn deref(&self) -> &Self::Target {
        &self._typ.typ.value
    }
}

impl<'ast, Id> DerefMut for AstType<'ast, Id> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self._typ.typ.value
    }
}

impl<Id: fmt::Debug> fmt::Debug for AstType<'_, Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("AstType")
            .field("metadata", &self._typ.metadata)
            .field("typ", &self._typ.typ)
            .finish()
    }
}

impl<Id: AsRef<str> + AsId<Id>> fmt::Display for AstType<'_, Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", types::TypeFormatter::new(self))
    }
}

impl<Id> HasSpan for AstType<'_, Id> {
    fn span(&self) -> Span<BytePos> {
        self._typ.typ.span
    }
}

impl<'ast, Id> TypePtr for AstType<'ast, Id> {
    type Id = Id;
    type SpannedId = Spanned<Id, BytePos>;
    type Types = &'ast mut [AstType<'ast, Id>];
    type Generics = &'ast mut [Generic<Id>];
    type Fields = &'ast mut [Field<Self::SpannedId, Self>];
    type TypeFields = &'ast mut [Field<Self::SpannedId, Alias<Id, Self>>];
}

pub trait HasMetadata {
    fn metadata(&self) -> Option<&Metadata>;

    fn comment(&self) -> Option<&Comment> {
        self.metadata()
            .and_then(|metadata| metadata.comment.as_ref())
    }
}

impl<Id> HasMetadata for AstType<'_, Id> {
    fn metadata(&self) -> Option<&Metadata> {
        self._typ.metadata.metadata.as_ref().map(|m| &**m)
    }
}

impl<'ast, Id> AstType<'ast, Id> {
    pub fn new(
        arena: ArenaRef<'_, 'ast, Id>,
        typ: Spanned<Type<Id, AstType<'ast, Id>>, BytePos>,
    ) -> Self {
        AstType {
            _typ: arena.alloc(InnerAstType {
                metadata: Default::default(),
                typ,
            }),
        }
    }

    pub fn new_no_loc(arena: ArenaRef<'_, 'ast, Id>, typ: Type<Id, AstType<'ast, Id>>) -> Self {
        Self::new(arena, pos::spanned2(0.into(), 0.into(), typ))
    }

    pub fn with_metadata<T>(
        arena: ArenaRef<'_, 'ast, Id>,
        metadata: T,
        typ: Spanned<Type<Id, AstType<'ast, Id>>, BytePos>,
    ) -> Self
    where
        T: Into<BaseMetadata<'ast>>,
    {
        AstType {
            _typ: arena.alloc(InnerAstType {
                metadata: metadata.into(),
                typ,
            }),
        }
    }

    pub fn set_metadata<T>(&mut self, metadata: T)
    where
        T: Into<BaseMetadata<'ast>>,
    {
        self._typ.metadata = metadata.into();
    }

    pub fn remove_single_forall(&mut self) -> &mut AstType<'ast, Id> {
        match self._typ.typ.value {
            Type::Forall(_, ref mut typ) => typ,
            _ => self,
        }
    }

    pub fn span_mut(&mut self) -> &mut Span<BytePos> {
        &mut self._typ.typ.span
    }
}

impl<'ast, Id> AsMut<SpannedAstType<'ast, Id>> for AstType<'ast, Id> {
    fn as_mut(&mut self) -> &mut SpannedAstType<'ast, Id> {
        &mut self._typ.typ
    }
}

pub type KindedIdent<Id> = TypedIdent<Id, ArcKind>;

#[derive(Clone, Eq, PartialEq, Hash, Debug, Default)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(de_parameters = "U", deserialize_state = "Seed<Id, U>")
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "
           T: DeserializeState<'de, Seed<Id, U>>,
           U: Clone
                + TypePtr<Id = Id>
                + From<Type<Id, U>>
                + std::any::Any
                + DeserializeState<'de, Seed<Id, U>>,
           Id: DeserializeState<'de, Seed<Id, U>>
                + Clone
                + std::any::Any
                + DeserializeState<'de, Seed<Id, U>>"))
)]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
pub struct TypedIdent<Id = Symbol, T = ArcType<Id>> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub typ: T,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
}

impl<Id, T> TypedIdent<Id, T>
where
    T: Default,
{
    pub fn new(name: Id) -> TypedIdent<Id, T> {
        TypedIdent {
            typ: T::default(),
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

#[derive(Eq, PartialEq, Debug, AstClone)]
pub enum PatternField<'ast, Id> {
    Type {
        name: Spanned<Id, BytePos>,
    },
    Value {
        name: Spanned<Id, BytePos>,
        value: Option<SpannedPattern<'ast, Id>>,
    },
}

impl<Id> PatternField<'_, Id> {
    pub fn name(&self) -> &Spanned<Id, BytePos> {
        match self {
            PatternField::Type { name } | PatternField::Value { name, .. } => name,
        }
    }
}

#[derive(Eq, PartialEq, Debug, AstClone)]
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
        fields: &'ast mut [PatternField<'ast, Id>],
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

// Safeguard against growing Pattern
#[cfg(target_pointer_width = "64")]
const _: [u8; 48] = [0; std::mem::size_of::<Pattern<'static, Symbol>>()];

pub fn pattern_names<'a, 'ast, Id>(
    fields: &'a [PatternField<'ast, Id>],
) -> impl Iterator<Item = &'a Spanned<Id, BytePos>> + Captures<'ast> {
    fields.iter().map(|field| field.name())
}

pub fn pattern_values<'a, 'ast, Id>(
    fields: &'a [PatternField<'ast, Id>],
) -> impl Iterator<
    Item = (
        &'a Spanned<Id, BytePos>,
        &'a Option<SpannedPattern<'ast, Id>>,
    ),
> {
    fields.iter().filter_map(|field| match field {
        PatternField::Type { .. } => None,
        PatternField::Value { name, value } => Some((name, value)),
    })
}

pub fn pattern_values_mut<'a, 'ast, Id>(
    fields: &'a mut [PatternField<'ast, Id>],
) -> impl Iterator<
    Item = (
        &'a mut Spanned<Id, BytePos>,
        &'a mut Option<SpannedPattern<'ast, Id>>,
    ),
> {
    fields.iter_mut().filter_map(|field| match field {
        PatternField::Type { .. } => None,
        PatternField::Value { name, value } => Some((name, value)),
    })
}

#[doc(hidden)]
pub trait Captures<'a> {}
impl<T> Captures<'_> for T {}

pub fn pattern_types<'a, 'ast, Id>(
    fields: &'a mut [PatternField<'ast, Id>],
) -> impl Iterator<Item = &'a mut Spanned<Id, BytePos>> + Captures<'ast> {
    fields.iter_mut().filter_map(|field| match field {
        PatternField::Type { name } => Some(name),
        PatternField::Value { .. } => None,
    })
}

impl<Id> Default for Pattern<'_, Id> {
    fn default() -> Self {
        Pattern::Error
    }
}

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct Alternative<'ast, Id> {
    pub pattern: SpannedPattern<'ast, Id>,
    pub expr: SpannedExpr<'ast, Id>,
}

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct Array<'ast, Id> {
    pub typ: ArcType<Id>,
    pub exprs: &'ast mut [SpannedExpr<'ast, Id>],
}

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct Lambda<'ast, Id> {
    pub id: TypedIdent<Id>,
    pub args: &'ast mut [Argument<SpannedIdent<Id>>],
    pub body: &'ast mut SpannedExpr<'ast, Id>,
}

pub type SpannedExpr<'ast, Id> = Spanned<Expr<'ast, Id>, BytePos>;

pub type SpannedIdent<Id> = Spanned<TypedIdent<Id>, BytePos>;

pub type SpannedAlias<'ast, Id> = Spanned<AliasData<Id, AstType<'ast, Id>>, BytePos>;

pub type SpannedAstType<'ast, Id> = Spanned<Type<Id, AstType<'ast, Id>>, BytePos>;

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct ExprField<'ast, Id, E> {
    pub metadata: BaseMetadata<'ast>,
    pub name: Spanned<Id, BytePos>,
    pub value: Option<E>,
}

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct Do<'ast, Id> {
    pub id: Option<SpannedPattern<'ast, Id>>,
    pub typ: Option<AstType<'ast, Id>>,
    pub bound: &'ast mut SpannedExpr<'ast, Id>,
    pub body: &'ast mut SpannedExpr<'ast, Id>,
    pub flat_map_id: Option<&'ast mut SpannedExpr<'ast, Id>>,
}

/// The representation of gluon's expression syntax
#[derive(Eq, PartialEq, Debug, AstClone)]
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
    Match(
        &'ast mut SpannedExpr<'ast, Id>,
        &'ast mut [Alternative<'ast, Id>],
    ),
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
        types: &'ast mut [ExprField<'ast, Id, ArcType<Id>>],
        exprs: &'ast mut [ExprField<'ast, Id, SpannedExpr<'ast, Id>>],
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
    TypeBindings(
        &'ast mut [TypeBinding<'ast, Id>],
        &'ast mut SpannedExpr<'ast, Id>,
    ),
    /// A group of sequenced expressions
    Block(&'ast mut [SpannedExpr<'ast, Id>]),
    Do(&'ast mut Do<'ast, Id>),
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

// Safeguard against growing Expr
#[cfg(target_pointer_width = "64")]
const _: [u8; 64] = [0; std::mem::size_of::<Expr<'static, Symbol>>()];

impl<'ast, Id> Expr<'ast, Id> {
    pub fn rec_let_bindings(
        arena: ArenaRef<'_, 'ast, Id>,
        binds: impl IntoIterator<Item = ValueBinding<'ast, Id>>,
        expr: SpannedExpr<'ast, Id>,
    ) -> Self {
        let binds = arena.alloc_extend(binds);
        if binds.is_empty() {
            expr.value
        } else {
            Expr::LetBindings(ValueBindings::Recursive(binds), arena.alloc(expr))
        }
    }

    pub fn annotated<'a>(
        arena: ArenaRef<'_, 'ast, Id>,
        expr: SpannedExpr<'ast, Id>,
        typ: ArcType<Id>,
    ) -> SpannedExpr<'ast, Id>
    where
        Id: From<&'a str> + Clone,
    {
        pos::spanned(expr.span, Expr::Annotated(arena.alloc(expr), typ))
    }

    pub fn let_binding(
        arena: ArenaRef<'_, 'ast, Id>,
        bind: ValueBinding<'ast, Id>,
        expr: SpannedExpr<'ast, Id>,
    ) -> Self {
        Expr::LetBindings(ValueBindings::Plain(arena.alloc(bind)), arena.alloc(expr))
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
        arena: ArenaRef<'_, 'ast, Id>,
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

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct TypeBinding<'ast, Id> {
    pub metadata: BaseMetadata<'ast>,
    pub name: Spanned<Id, BytePos>,
    pub alias: SpannedAlias<'ast, Id>,
    pub finalized_alias: Option<Alias<Id, ArcType<Id>>>,
}

impl<Id> TypeBinding<'_, Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start(), self.alias.span.end())
    }
}

#[derive(Clone, Default, Eq, PartialEq, Debug, Hash, AstClone)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Argument<N> {
    pub arg_type: ArgType,
    pub name: N,
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

#[derive(Eq, PartialEq, Debug, AstClone)]
pub enum ValueBindings<'ast, Id> {
    Plain(&'ast mut ValueBinding<'ast, Id>),
    Recursive(&'ast mut [ValueBinding<'ast, Id>]),
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

#[derive(Eq, PartialEq, Debug, AstClone)]
pub struct ValueBinding<'ast, Id> {
    pub metadata: BaseMetadata<'ast>,
    pub name: SpannedPattern<'ast, Id>,
    pub typ: Option<AstType<'ast, Id>>,
    pub resolved_type: ArcType<Id>,
    pub args: &'ast mut [Argument<SpannedIdent<Id>>],
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

    fn visit_alias(&mut self, alias: &'a $($mut)* SpannedAlias<'ast, Self::Ident>) {
        walk_alias(self, alias)
    }
    fn visit_spanned_ident(&mut self, _: &'a $($mut)* Spanned<Self::Ident, BytePos>) {}
    fn visit_typ(&mut self, _: &'a $($mut)* ArcType<Self::Ident>) {}
    fn visit_ast_type(&mut self, s: &'a $($mut)* AstType<'ast, Self::Ident>) {
        walk_ast_type(self, s);
    }
}

pub fn walk_alias<'a, 'ast, V>(
    v: &mut V,
    alias: &'a $($mut)* SpannedAlias<'ast, V::Ident>,
)
    where V: ?Sized + $trait_name<'a, 'ast>,
{
    v.visit_ast_type(alias.value.$unresolved_type());
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
                for arg in &$($mut)* *bind.args {
                    v.visit_spanned_typed_ident(&$($mut)* arg.name);
                }
                v.visit_typ(&$($mut)* bind.resolved_type);
                v.visit_expr(&$($mut)* bind.expr);
                if let Some(ref $($mut)* ast_type) = bind.typ {
                    v.visit_ast_type(ast_type)
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
            for alt in &$($mut)* **alts {
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
            for typ in &$($mut)* **types {
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
            ref $($mut)* typ,
            ref $($mut)* bound,
            ref $($mut)* body,
            ref $($mut)* flat_map_id,
        }) => {
            if let Some(id) = id {
                v.visit_pattern(id);
            }
            if let Some(ast_type) = typ {
                v.visit_ast_type(ast_type)
            }
            v.visit_expr(bound);
            v.visit_expr(body);
            if let Some(ref $($mut)* flat_map_id) = *flat_map_id {
                v.visit_expr(flat_map_id);
            }
        }

        Expr::Lambda(ref $($mut)* lambda) => {
            v.visit_ident(&$($mut)* lambda.id);
            for arg in &$($mut)* *lambda.args {
                v.visit_spanned_typed_ident(&$($mut)* arg.name);
            }
            v.visit_expr(&$($mut)* lambda.body);
        }
        Expr::TypeBindings(ref $($mut)* bindings, ref $($mut)* expr) => {
            for binding in &$($mut)* **bindings {
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
    match p {
        Pattern::As(id, pat) => {
            v.visit_spanned_ident(id);
            v.visit_pattern(pat);
        }
        Pattern::Constructor(id, args) => {
            v.visit_ident(id);
            for arg in &$($mut)* **args {
                v.visit_pattern(arg);
            }
        }
        Pattern::Record {
            typ,
            fields,
            ..
        } => {
            v.visit_typ(typ);
            for field in &$($mut)* **fields {
                match field {
                    PatternField::Value { name, value: ref $($mut)* pattern, } => {
                        v.visit_spanned_ident(name);
                        if let Some(pattern) = pattern {
                        v.visit_pattern(pattern);
                        }
                    }
                    PatternField::Type { name, .. } => {
                        v.visit_spanned_ident(name);
                    }
                }
            }
        }
        Pattern::Tuple {
            typ,
            elems,
        } => {
            v.visit_typ(typ);
            for elem in &$($mut)* **elems {
                v.visit_pattern(elem);
            }
        }
        Pattern::Ident(id) => v.visit_ident(id),
        Pattern::Literal(_) | Pattern::Error => (),
    }
}

pub fn walk_ast_type<'a, 'ast, V: ?Sized + $trait_name<'a, 'ast>>(
    v: &mut V,
    s: &'a $($mut)* AstType<'ast, V::Ident>,
) {
    match **s {
        Type::Hole | Type::Opaque | Type::Error | Type::Builtin(_) => (),
        Type::Forall(_, ref $($mut)* ast_type) => {
            v.visit_ast_type(ast_type);
        }
        Type::Function(_, ref $($mut)* arg, ref $($mut)* ret) => {
            v.visit_ast_type(arg);
            v.visit_ast_type(ret);
        }
        Type::App(ref $($mut)* ast_type, ref $($mut)* ast_types) => {
            for ast_type in & $($mut)* **ast_types {
                v.visit_ast_type(ast_type);
            }
            v.visit_ast_type(ast_type)
        }
        Type::Record(ref $($mut)* ast_type) => v.visit_ast_type(ast_type),
        Type::Variant(ref $($mut)* ast_type) => v.visit_ast_type(ast_type),
        Type::Effect(ref $($mut)* ast_type) => v.visit_ast_type(ast_type),
        Type::EmptyRow => (),
        Type::ExtendRow {
            ref $($mut)* fields,
            ref $($mut)* rest,
        } => {
            for field in & $($mut)* **fields {
                v.visit_spanned_ident(& $($mut)* field.name);
                v.visit_ast_type(&$($mut)* field.typ);
            }
            v.visit_ast_type(rest);
        }
        Type::ExtendTypeRow {
            ref $($mut)* types,
            ref $($mut)* rest,
        } => {
            for field in & $($mut)* **types {
                v.visit_spanned_ident(& $($mut)* field.name);
                if let Some(alias) = field.typ.$try_get_alias() {
                    v.visit_ast_type(alias.$unresolved_type());
                }
            }
            v.visit_ast_type(rest);
        }
        Type::Alias(ref $($mut)* alias) => {
            if let Some(alias) = alias.$try_get_alias() {
                v.visit_ast_type(alias.$unresolved_type());
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

impl Typed for OwnedExpr<Symbol> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType, String> {
        self.expr().try_type_of(env)
    }
}

impl Typed for RootExpr<Symbol> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &dyn TypeEnv<Type = ArcType>) -> Result<ArcType, String> {
        self.expr().try_type_of(env)
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
    match c {
        b'!' | b'#' | b'$' | b'%' | b'&' | b'*' | b'+' | b'-' | b'.' | b'/' | b'<' | b'='
        | b'>' | b'?' | b'@' | b'\\' | b'^' | b'|' | b'~' | b':' => true,
        _ => false,
    }
}

pub fn is_constructor(s: &str) -> bool {
    s.rsplit('.')
        .next()
        .unwrap()
        .starts_with(char::is_uppercase)
}

pub fn expr_to_path(expr: &SpannedExpr<Symbol>, path: &mut String) -> Result<(), &'static str> {
    match &expr.value {
        Expr::Ident(id) => {
            path.push_str(id.name.declared_name());
            Ok(())
        }
        Expr::Projection(expr, id, _) => {
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

pub struct ArenaRef<'a, 'ast, Id>(
    &'ast Arena<'ast, Id>,
    PhantomData<&'a &'ast Arena<'ast, Id>>,
);

impl<'a, 'ast, Id> Copy for ArenaRef<'a, 'ast, Id> {}
impl<'a, 'ast, Id> Clone for ArenaRef<'a, 'ast, Id> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData)
    }
}

impl<'a, 'ast, Id> ArenaRef<'a, 'ast, Id> {
    pub fn alloc<T>(self, value: T) -> &'ast mut T
    where
        T: AstAlloc<'ast, Id> + 'ast,
    {
        value.alloc(&self.0)
    }

    pub fn alloc_extend<T>(self, iter: impl IntoIterator<Item = T>) -> &'ast mut [T]
    where
        T: AstAlloc<'ast, Id> + 'ast,
    {
        T::alloc_extend(iter, &self.0)
    }
}

pub trait AstAlloc<'ast, Id>: Sized {
    fn alloc(self, arena: &'ast Arena<'ast, Id>) -> &'ast mut Self;
    fn alloc_extend(
        iter: impl IntoIterator<Item = Self>,
        arena: &'ast Arena<'ast, Id>,
    ) -> &'ast mut [Self];
}

macro_rules! impl_ast_arena {
    ($( $ty: ty => $field: ident ),+ $(,)?) => {

        pub struct Arena<'ast, Id> {
        $(
            $field: typed_arena::Arena<$ty>,
        )+
        }

        impl<'ast, Id> Arena<'ast, Id> {
            pub unsafe fn new(_: &'ast InvariantLifetime<'ast>) -> Self {
                Arena {
                    $(
                        $field: typed_arena::Arena::new(),
                    )+
                }
            }

            pub fn borrow(&'ast self) -> ArenaRef<'_, 'ast, Id> {
                ArenaRef(self, PhantomData)
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

        $(
        impl<'ast, Id> AstAlloc<'ast, Id> for $ty {
            fn alloc(self, arena: &'ast Arena<'ast, Id>) -> &'ast mut Self {
                arena.$field.alloc(self)
            }

            fn alloc_extend(
                iter: impl IntoIterator<Item = Self>,
                arena: &'ast Arena<'ast, Id>,
            ) -> &'ast mut [Self] {
                arena.$field.alloc_extend(iter)
            }
        }
        )+
    };
}

impl_ast_arena! {
    SpannedExpr<'ast, Id> => exprs,
    SpannedPattern<'ast, Id> => patterns,
    PatternField<'ast, Id> => pattern_field,
    ExprField<'ast, Id, ArcType<Id>> => expr_field_types,
    ExprField<'ast, Id, SpannedExpr<'ast, Id>> => expr_field_exprs,
    TypeBinding<'ast, Id> => type_bindings,
    ValueBinding<'ast, Id> => value_bindings,
    Do<'ast, Id> => do_exprs,
    Alternative<'ast, Id> => alts,
    Argument<SpannedIdent<Id>> => args,
    InnerAstType<'ast, Id> => types,
    AstType<'ast, Id> => type_ptrs,
    Generic<Id> => generics,
    Field<Spanned<Id, BytePos>, AstType<'ast, Id>> => type_fields,
    Field<Spanned<Id, BytePos>, Alias<Id, AstType<'ast, Id>>> => type_type_fields,
    Metadata => metadata,
}

#[doc(hidden)]
#[derive(Default)]
pub struct InvariantLifetime<'a>(std::marker::PhantomData<fn(&'a ()) -> &'a ()>);

// Copied from the compact_arena crate
#[macro_export]
macro_rules! mk_ast_arena {
    ($name: ident) => {
        let tag = $crate::ast::InvariantLifetime::default();
        let $name = unsafe { std::sync::Arc::new($crate::ast::Arena::new(&tag)) };
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

pub struct RootExpr<Id: 'static> {
    // Only used to keep `expr` alive
    #[allow(dead_code)]
    arena: Arc<Arena<'static, Id>>,
    expr: *mut SpannedExpr<'static, Id>,
}

impl<Id: 'static> Default for RootExpr<Id> {
    fn default() -> Self {
        mk_ast_arena!(arena);
        let expr = arena.alloc(SpannedExpr::default());
        RootExpr::new(arena.clone(), expr)
    }
}

impl<Id: Eq> Eq for RootExpr<Id> {}
impl<Id: PartialEq> PartialEq for RootExpr<Id> {
    fn eq(&self, other: &Self) -> bool {
        self.expr() == other.expr()
    }
}

impl<Id: fmt::Debug> fmt::Debug for RootExpr<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.expr().fmt(f)
    }
}

impl<Id> RootExpr<Id> {
    pub fn new<'ast>(arena: Arc<Arena<'ast, Id>>, expr: &'ast mut SpannedExpr<'ast, Id>) -> Self {
        // SAFETY Arena<'ast> can only be constructed with an invariant lifetime which means that
        // `expr` must come from that arena. This locks the lifetime of `expr` to `arena` so that
        // the expression won't be dropped before the arena is
        unsafe {
            Self {
                arena: mem::transmute::<Arc<Arena<Id>>, Arc<Arena<Id>>>(arena),
                expr: mem::transmute::<*mut SpannedExpr<Id>, *mut SpannedExpr<Id>>(expr),
            }
        }
    }

    pub fn with_arena<R>(
        &mut self,
        f: impl for<'ast> FnOnce(&'ast Arena<'ast, Id>, &'ast mut SpannedExpr<'ast, Id>) -> R,
    ) -> R {
        let (arena, expr) = self.arena_expr();
        f(arena, expr)
    }

    pub fn expr(&self) -> &SpannedExpr<'_, Id> {
        unsafe { mem::transmute::<&SpannedExpr<Id>, &SpannedExpr<Id>>(&*self.expr) }
    }

    pub fn expr_mut(&mut self) -> &mut SpannedExpr<'_, Id> {
        self.arena_expr().1
    }

    pub fn arena_expr(&mut self) -> (&Arena<'_, Id>, &mut SpannedExpr<'_, Id>) {
        unsafe {
            (
                mem::transmute::<&Arena<Id>, &Arena<Id>>(&self.arena),
                mem::transmute::<&mut SpannedExpr<Id>, &mut SpannedExpr<Id>>(&mut *self.expr),
            )
        }
    }

    pub fn try_into_send(self) -> Result<OwnedExpr<Id>, Self> {
        match Arc::try_unwrap(self.arena) {
            Ok(arena) => Ok(OwnedExpr {
                arena,
                expr: self.expr,
            }),
            Err(arena) => Err(Self {
                arena,
                expr: self.expr,
            }),
        }
    }
}

pub struct OwnedArena<'ast, Id>(&'ast Arena<'ast, Id>);

// SAFETY OwnedArena is only created if we own the arena. Since `Arena` is `Send` we then we can
// construct one instance of this at a time which is send (like a mutable refernce, but we can't
// give out a mutable reference itself since that could be used to free the arena).
unsafe impl<'ast, Id> Send for OwnedArena<'ast, Id> {}

impl<'ast, Id> OwnedArena<'ast, Id> {
    pub fn borrow(&self) -> ArenaRef<'_, 'ast, Id> {
        ArenaRef(self.0, PhantomData)
    }

    pub fn alloc<T>(&self, value: T) -> &'ast mut T
    where
        T: AstAlloc<'ast, Id>,
    {
        self.0.alloc(value)
    }

    pub fn alloc_extend<T>(&self, iter: impl IntoIterator<Item = T>) -> &'ast mut [T]
    where
        T: AstAlloc<'ast, Id>,
    {
        self.0.alloc_extend(iter)
    }
}

pub struct OwnedExpr<Id: 'static> {
    // Only used to keep `expr` alive
    #[allow(dead_code)]
    arena: Arena<'static, Id>,
    expr: *mut SpannedExpr<'static, Id>,
}

impl<Id: 'static> Default for OwnedExpr<Id> {
    fn default() -> Self {
        RootExpr::default().try_into_send().ok().unwrap_or_default()
    }
}

impl<Id: Eq> Eq for OwnedExpr<Id> {}
impl<Id: PartialEq> PartialEq for OwnedExpr<Id> {
    fn eq(&self, other: &Self) -> bool {
        self.expr() == other.expr()
    }
}

impl<Id: fmt::Debug> fmt::Debug for OwnedExpr<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.expr().fmt(f)
    }
}

/// Since the `Arena` is no longer accessible it if `self` is the only owner of
/// the arena we can implement `Send` and  `Sync`
unsafe impl<Id> Send for OwnedExpr<Id>
where
    Id: Send,
    SpannedExpr<'static, Id>: Send,
{
}

unsafe impl<Id> Sync for OwnedExpr<Id>
where
    Id: Sync,
    SpannedExpr<'static, Id>: Sync,
{
}

impl<Id> OwnedExpr<Id> {
    pub fn with_arena<R>(
        &mut self,
        f: impl for<'ast> FnOnce(OwnedArena<'ast, Id>, &'ast mut SpannedExpr<'ast, Id>) -> R,
    ) -> R {
        let (arena, expr) = self.arena_expr();
        f(arena, expr)
    }

    pub fn expr(&self) -> &SpannedExpr<'_, Id> {
        unsafe { mem::transmute::<&SpannedExpr<Id>, &SpannedExpr<Id>>(&*self.expr) }
    }

    pub fn expr_mut(&mut self) -> &mut SpannedExpr<'_, Id> {
        self.arena_expr().1
    }

    pub fn arena_expr(&mut self) -> (OwnedArena<'_, Id>, &mut SpannedExpr<'_, Id>) {
        unsafe {
            (
                OwnedArena(mem::transmute::<&Arena<Id>, &Arena<Id>>(&self.arena)),
                mem::transmute::<&mut SpannedExpr<Id>, &mut SpannedExpr<Id>>(&mut *self.expr),
            )
        }
    }
}

pub trait AstClone<'ast, Id> {
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self;
}

impl<'ast, Id, T> AstClone<'ast, Id> for Option<T>
where
    T: AstClone<'ast, Id>,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        self.as_ref().map(|x| x.ast_clone(arena))
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for PhantomData<T> {
    fn ast_clone(&self, _arena: ArenaRef<'_, 'ast, Id>) -> Self {
        PhantomData
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for Arc<[crate::types::AliasData<Id, T>]>
where
    Id: Clone + AstClone<'ast, Id>,
    T: AstClone<'ast, Id> + TypePtr<Id = Id>,
    T::Generics: AstClone<'ast, Id>,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        Arc::from(self.iter().map(|e| e.ast_clone(arena)).collect::<Vec<_>>())
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for Vec<T>
where
    T: Clone,
{
    fn ast_clone(&self, _arena: ArenaRef<'_, 'ast, Id>) -> Self {
        self.clone()
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for crate::types::AppVec<T>
where
    T: Clone,
{
    fn ast_clone(&self, _arena: ArenaRef<'_, 'ast, Id>) -> Self {
        self.clone()
    }
}

impl<'ast, Id, T, P> AstClone<'ast, Id> for Spanned<T, P>
where
    T: AstClone<'ast, Id>,
    P: Clone,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        pos::spanned(self.span.clone(), self.value.ast_clone(arena))
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for TypedIdent<Id, T>
where
    Id: Clone,
    T: AstClone<'ast, Id>,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        TypedIdent {
            name: self.name.clone(),
            typ: self.typ.ast_clone(arena),
        }
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for &'ast mut [T]
where
    T: AstClone<'ast, Id> + AstAlloc<'ast, Id>,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        let elems: Vec<_> = self.iter().map(|e| e.ast_clone(arena)).collect();
        arena.alloc_extend(elems)
    }
}

impl<'ast, Id, T> AstClone<'ast, Id> for &'ast mut T
where
    T: AstClone<'ast, Id> + AstAlloc<'ast, Id>,
{
    fn ast_clone(&self, arena: ArenaRef<'_, 'ast, Id>) -> Self {
        arena.alloc((**self).ast_clone(arena))
    }
}

macro_rules! impl_ast_clone {
    ($($ty: ty $(where [$($where_: tt)*])? ,)*) => {
        $(
            impl<'ast, Id> AstClone<'ast, Id> for $ty
                $( where $($where_)* )?
            {
                fn ast_clone(&self, _arena: ArenaRef<'_, 'ast, Id>) -> Self {
                    self.clone()
                }
            }
        )*
    };
}

impl_ast_clone! {
    ArcType<Id>,
    Literal,
    Metadata,
    crate::types::TypeVariable,
    ArcKind,
    crate::types::ArgType,
    crate::types::BuiltinType,
    usize,
    u32,
    bool,
    BytePos,
    Symbol,
}
