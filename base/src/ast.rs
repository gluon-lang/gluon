//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use pos::{self, BytePos, HasSpan, Span, Spanned};
use symbol::Symbol;
use types::{self, Alias, AliasData, ArcType, ArgType, Generic, Type, TypeEnv};
use ordered_float::NotNaN;

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
pub struct AstType<Id> {
    _typ: Box<(Option<Comment>, Spanned<Type<Id, AstType<Id>>, BytePos>)>,
}

impl<Id> Deref for AstType<Id> {
    type Target = Type<Id, AstType<Id>>;

    fn deref(&self) -> &Self::Target {
        &self._typ.1.value
    }
}

impl<Id> DerefMut for AstType<Id> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self._typ.1.value
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
            _typ: Box::new((None, typ)),
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
        self._typ.1.span
    }
}

impl<Id> Commented for AstType<Id> {
    fn comment(&self) -> Option<&Comment> {
        self._typ.0.as_ref()
    }
}

impl<Id> AstType<Id> {
    pub fn with_comment<T>(comment: T, typ: Spanned<Type<Id, AstType<Id>>, BytePos>) -> Self
    where
        T: Into<Option<Comment>>,
    {
        AstType {
            _typ: Box::new((comment.into(), typ)),
        }
    }

    pub fn set_comment<T>(&mut self, comment: T)
    where
        T: Into<Option<Comment>>,
    {
        self._typ.0 = comment.into();
    }

    pub fn into_inner(self) -> Type<Id, Self> {
        self._typ.1.value
    }

    pub fn as_mut(&mut self) -> &mut SpannedAstType<Id> {
        &mut self._typ.1
    }

    pub fn params_mut(&mut self) -> &mut [Generic<Id>] {
        match self._typ.1.value {
            Type::Forall(ref mut params, _, _) => params,
            Type::App(ref mut id, _) => id.params_mut(),
            _ => &mut [],
        }
    }

    pub fn remove_single_forall(&mut self) -> &mut AstType<Id> {
        match self._typ.1.value {
            Type::Forall(_, ref mut typ, _) => return typ,
            _ => self,
        }
    }
}

pub trait Commented {
    fn comment(&self) -> Option<&Comment>;
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum CommentType {
    Block,
    Line,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Comment {
    pub typ: CommentType,
    pub content: String,
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
            name: name,
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
    Float(NotNaN<f64>),
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
    As(Id, Box<SpannedPattern<Id>>),
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
    pub args: Vec<Argument<Id>>,
    pub body: Box<SpannedExpr<Id>>,
}

pub type SpannedExpr<Id> = Spanned<Expr<Id>, BytePos>;

pub type SpannedIdent<Id> = Spanned<TypedIdent<Id>, BytePos>;

pub type SpannedAlias<Id> = Spanned<AliasData<Id, AstType<Id>>, BytePos>;

pub type SpannedAstType<Id> = Spanned<Type<Id, AstType<Id>>, BytePos>;

#[derive(Clone, PartialEq, Debug)]
pub struct ExprField<Id, E> {
    pub comment: Option<Comment>,
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
    LetBindings(Vec<ValueBinding<Id>>, Box<SpannedExpr<Id>>),
    /// Declare a series of type aliases
    TypeBindings(Vec<TypeBinding<Id>>, Box<SpannedExpr<Id>>),
    /// A group of sequenced expressions
    Block(Vec<SpannedExpr<Id>>),
    Do(Do<Id>),
    /// An invalid expression
    Error(
        /// Provides a hint of what type the expression would have, if any
        Option<ArcType<Id>>,
    ),
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub comment: Option<Comment>,
    pub name: Spanned<Id, BytePos>,
    pub alias: SpannedAlias<Id>,
    pub finalized_alias: Option<Alias<Id, ArcType<Id>>>,
}

impl<Id> TypeBinding<Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start, self.alias.span.end)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Argument<Id> {
    pub arg_type: ArgType,
    pub name: SpannedIdent<Id>,
}

impl<Id> Argument<Id> {
    pub fn explicit(name: SpannedIdent<Id>) -> Self {
        Argument {
            arg_type: ArgType::Explicit,
            name,
        }
    }

    pub fn implicit(name: SpannedIdent<Id>) -> Self {
        Argument {
            arg_type: ArgType::Implicit,
            name,
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueBinding<Id> {
    pub comment: Option<Comment>,
    pub name: SpannedPattern<Id>,
    pub typ: Option<AstType<Id>>,
    pub resolved_type: ArcType<Id>,
    pub args: Vec<Argument<Id>>,
    pub expr: SpannedExpr<Id>,
}

impl<Id> ValueBinding<Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start, self.expr.span.end)
    }
}

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overridden the user will need to
/// call `walk_mut_*` to continue traversing the tree.
pub trait MutVisitor<'a> {
    type Ident: 'a;

    fn visit_expr(&mut self, e: &'a mut SpannedExpr<Self::Ident>) {
        walk_mut_expr(self, e);
    }

    fn visit_pattern(&mut self, e: &'a mut SpannedPattern<Self::Ident>) {
        walk_mut_pattern(self, &mut e.value);
    }

    fn visit_spanned_typed_ident(&mut self, id: &'a mut SpannedIdent<Self::Ident>) {
        self.visit_ident(&mut id.value)
    }

    fn visit_ident(&mut self, id: &'a mut TypedIdent<Self::Ident>) {
        self.visit_typ(&mut id.typ)
    }

    fn visit_alias(&mut self, alias: &'a mut SpannedAlias<Self::Ident>) {
        walk_mut_alias(self, alias)
    }
    fn visit_spanned_ident(&mut self, _: &'a mut Spanned<Self::Ident, BytePos>) {}
    fn visit_typ(&mut self, _: &'a mut ArcType<Self::Ident>) {}
    fn visit_ast_type(&mut self, s: &'a mut SpannedAstType<Self::Ident>) {
        walk_mut_ast_type(self, s);
    }
}

pub fn walk_mut_alias<'a, V: ?Sized + MutVisitor<'a>>(
    v: &mut V,
    alias: &'a mut SpannedAlias<V::Ident>,
) {
    v.visit_ast_type(&mut alias.value.unresolved_type_mut()._typ.1);
}

pub fn walk_mut_expr<'a, V: ?Sized + MutVisitor<'a>>(v: &mut V, e: &'a mut SpannedExpr<V::Ident>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(pred);
            v.visit_expr(if_true);
            v.visit_expr(if_false);
        }
        Expr::Infix {
            ref mut lhs,
            ref mut op,
            ref mut rhs,
            ref mut implicit_args,
        } => {
            v.visit_expr(lhs);
            v.visit_spanned_typed_ident(op);
            v.visit_expr(rhs);
            for arg in implicit_args {
                v.visit_expr(arg);
            }
        }
        Expr::LetBindings(ref mut bindings, ref mut body) => {
            for bind in bindings {
                v.visit_pattern(&mut bind.name);
                for arg in &mut bind.args {
                    v.visit_spanned_typed_ident(&mut arg.name);
                }
                v.visit_typ(&mut bind.resolved_type);
                v.visit_expr(&mut bind.expr);
                if let Some(ref mut ast_type) = bind.typ {
                    v.visit_ast_type(&mut ast_type._typ.1)
                }
            }
            v.visit_expr(body);
        }
        Expr::App {
            ref mut func,
            ref mut implicit_args,
            ref mut args,
        } => {
            v.visit_expr(func);
            for arg in implicit_args {
                v.visit_expr(arg);
            }
            for arg in args {
                v.visit_expr(arg);
            }
        }
        Expr::Projection(ref mut expr, _, ref mut typ) => {
            v.visit_expr(expr);
            v.visit_typ(typ);
        }
        Expr::Match(ref mut expr, ref mut alts) => {
            v.visit_expr(expr);
            for alt in alts {
                v.visit_pattern(&mut alt.pattern);
                v.visit_expr(&mut alt.expr);
            }
        }
        Expr::Array(ref mut a) => {
            v.visit_typ(&mut a.typ);
            for expr in &mut a.exprs {
                v.visit_expr(expr);
            }
        }
        Expr::Record {
            ref mut typ,
            ref mut types,
            ref mut exprs,
            ref mut base,
            ..
        } => {
            v.visit_typ(typ);
            for typ in types {
                v.visit_spanned_ident(&mut typ.name);
            }
            for field in exprs {
                v.visit_spanned_ident(&mut field.name);
                if let Some(ref mut expr) = field.value {
                    v.visit_expr(expr);
                }
            }
            if let Some(ref mut base) = *base {
                v.visit_expr(base);
            }
        }
        Expr::Tuple {
            ref mut typ,
            ref mut elems,
        } => {
            v.visit_typ(typ);
            for expr in elems {
                v.visit_expr(expr);
            }
        }
        Expr::Block(ref mut exprs) => for expr in exprs {
            v.visit_expr(expr);
        },

        Expr::Do(Do {
            ref mut id,
            ref mut bound,
            ref mut body,
            ref mut flat_map_id,
        }) => {
            v.visit_spanned_typed_ident(id);
            v.visit_expr(bound);
            v.visit_expr(body);
            if let Some(ref mut flat_map_id) = *flat_map_id {
                v.visit_expr(flat_map_id);
            }
        }

        Expr::Lambda(ref mut lambda) => {
            v.visit_ident(&mut lambda.id);
            for arg in &mut lambda.args {
                v.visit_spanned_typed_ident(&mut arg.name);
            }
            v.visit_expr(&mut lambda.body);
        }
        Expr::TypeBindings(ref mut bindings, ref mut expr) => {
            for binding in bindings.iter_mut() {
                v.visit_spanned_ident(&mut binding.name);
                v.visit_alias(&mut binding.alias);
            }
            v.visit_expr(expr)
        }
        Expr::Ident(ref mut id) => v.visit_ident(id),
        Expr::Literal(..) | Expr::Error(..) => (),
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_mut_pattern<'a, V: ?Sized + MutVisitor<'a>>(v: &mut V, p: &'a mut Pattern<V::Ident>) {
    match *p {
        Pattern::As(_, ref mut pat) => {
            v.visit_pattern(pat);
        }
        Pattern::Constructor(ref mut id, ref mut args) => {
            v.visit_ident(id);
            for arg in args {
                v.visit_pattern(arg);
            }
        }
        Pattern::Record {
            ref mut typ,
            ref mut fields,
            ..
        } => {
            v.visit_typ(typ);
            for field in fields {
                v.visit_spanned_ident(&mut field.name);
                if let Some(ref mut pattern) = field.value {
                    v.visit_pattern(pattern);
                }
            }
        }
        Pattern::Tuple {
            ref mut typ,
            ref mut elems,
        } => {
            v.visit_typ(typ);
            for elem in elems {
                v.visit_pattern(elem);
            }
        }
        Pattern::Ident(ref mut id) => v.visit_ident(id),
        Pattern::Literal(_) | Pattern::Error => (),
    }
}

pub fn walk_mut_ast_type<'a, V: ?Sized + MutVisitor<'a>>(
    v: &mut V,
    s: &'a mut SpannedAstType<V::Ident>,
) {
    match s.value {
        Type::Hole | Type::Opaque | Type::Builtin(_) => (),
        Type::Forall(_, ref mut ast_type, ref mut ast_types) => {
            v.visit_ast_type(&mut ast_type._typ.1);
            if let &mut Some(ref mut ast_types) = ast_types {
                for ast_type in ast_types {
                    v.visit_ast_type(&mut ast_type._typ.1);
                }
            }
        }
        Type::Function(_, ref mut arg, ref mut ret) => {
            v.visit_ast_type(&mut arg._typ.1);
            v.visit_ast_type(&mut ret._typ.1);
        }
        Type::App(ref mut ast_type, ref mut ast_types) => {
            for ast_type in ast_types.iter_mut() {
                v.visit_ast_type(&mut ast_type._typ.1);
            }
            v.visit_ast_type(&mut ast_type._typ.1)
        }
        Type::Record(ref mut ast_type) => v.visit_ast_type(&mut ast_type._typ.1),
        Type::Variant(ref mut ast_type) => v.visit_ast_type(&mut ast_type._typ.1),
        Type::EmptyRow => (),
        Type::ExtendRow {
            types: _,
            ref mut fields,
            ref mut rest,
        } => {
            for field in fields.iter_mut() {
                v.visit_ast_type(&mut field.typ._typ.1);
            }
            v.visit_ast_type(&mut rest._typ.1);
        }
        Type::Ident(_) => (),
        Type::Variable(_) => (),
        Type::Generic(_) => (),
        Type::Alias(_) => (),
        Type::Skolem(_) => (),
    }
}

pub trait Visitor<'a> {
    type Ident: 'a;

    fn visit_expr(&mut self, e: &'a SpannedExpr<Self::Ident>) {
        walk_expr(self, e);
    }

    fn visit_pattern(&mut self, e: &'a SpannedPattern<Self::Ident>) {
        walk_pattern(self, &e.value);
    }

    fn visit_typ(&mut self, _: &'a ArcType<Self::Ident>) {}
}

pub fn walk_expr<'a, V: ?Sized + Visitor<'a>>(v: &mut V, e: &'a SpannedExpr<V::Ident>) {
    match e.value {
        Expr::IfElse(ref pred, ref if_true, ref if_false) => {
            v.visit_expr(pred);
            v.visit_expr(if_true);
            v.visit_expr(if_false);
        }
        Expr::Infix {
            ref lhs,
            ref op,
            ref rhs,
            ref implicit_args,
        } => {
            v.visit_expr(lhs);
            v.visit_typ(&op.value.typ);
            v.visit_expr(rhs);
            for arg in implicit_args {
                v.visit_expr(arg);
            }
        }
        Expr::LetBindings(ref bindings, ref body) => {
            for bind in bindings {
                v.visit_pattern(&bind.name);
                v.visit_expr(&bind.expr);
            }
            v.visit_expr(body);
        }
        Expr::App {
            ref func,
            ref implicit_args,
            ref args,
        } => {
            v.visit_expr(func);
            for arg in implicit_args {
                v.visit_expr(arg);
            }
            for arg in args {
                v.visit_expr(arg);
            }
        }
        Expr::Projection(ref expr, _, ref typ) => {
            v.visit_expr(expr);
            v.visit_typ(typ);
        }
        Expr::Match(ref expr, ref alts) => {
            v.visit_expr(expr);
            for alt in alts {
                v.visit_pattern(&alt.pattern);
                v.visit_expr(&alt.expr);
            }
        }
        Expr::Array(ref a) => {
            v.visit_typ(&a.typ);
            for expr in &a.exprs {
                v.visit_expr(expr);
            }
        }
        Expr::Record {
            ref typ,
            ref exprs,
            ref base,
            ..
        } => {
            v.visit_typ(typ);
            for field in exprs {
                if let Some(ref expr) = field.value {
                    v.visit_expr(expr);
                }
            }
            if let Some(ref base) = *base {
                v.visit_expr(base);
            }
        }
        Expr::Tuple {
            elems: ref exprs, ..
        }
        | Expr::Block(ref exprs) => for expr in exprs {
            v.visit_expr(expr);
        },
        Expr::Do(Do {
            ref bound,
            ref body,
            ..
        }) => {
            v.visit_expr(bound);
            v.visit_expr(body);
        }
        Expr::Lambda(ref lambda) => {
            v.visit_typ(&lambda.id.typ);
            v.visit_expr(&lambda.body);
        }
        Expr::TypeBindings(_, ref expr) => v.visit_expr(expr),
        Expr::Ident(ref id) => v.visit_typ(&id.typ),
        Expr::Literal(..) | Expr::Error(..) => (),
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_pattern<'a, V: ?Sized + Visitor<'a>>(v: &mut V, p: &'a Pattern<V::Ident>) {
    match *p {
        Pattern::As(_, ref pat) => {
            v.visit_pattern(&pat);
        }
        Pattern::Constructor(ref id, ref args) => {
            v.visit_typ(&id.typ);
            for arg in args {
                v.visit_pattern(&arg);
            }
        }
        Pattern::Record {
            ref typ,
            ref fields,
            ..
        } => {
            v.visit_typ(typ);
            for field in fields {
                if let Some(ref pattern) = field.value {
                    v.visit_pattern(pattern);
                }
            }
        }
        Pattern::Tuple { ref typ, ref elems } => {
            v.visit_typ(typ);
            for elem in elems {
                v.visit_pattern(elem);
            }
        }
        Pattern::Ident(ref id) => v.visit_typ(&id.typ),
        Pattern::Literal(_) | Pattern::Error => (),
    }
}

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
            Expr::Error(ref typ) => Ok(typ.clone().unwrap_or_else(|| Type::hole())),
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
    // We don't want to panic if we attempt to get the return type of a hole so return a type hole
    // as the return type
    if arg_count == 0 || **alias_type == Type::Hole {
        return Ok(alias_type.clone());
    }

    let alias_type = alias_type.remove_forall_and_implicit_args();
    if let Some((_, ret)) = alias_type.as_function() {
        return get_return_type(env, ret, arg_count - 1);
    }

    let alias = {
        let alias_ident = alias_type.alias_ident().ok_or_else(|| {
            format!(
                "Expected function with {} more arguments, found {:?}",
                arg_count, alias_type
            )
        })?;

        env.find_type_info(alias_ident)
            .ok_or_else(|| format!("Unexpected type {} is not a function", alias_type))?
    };

    let typ = types::walk_move_type(alias.typ().into_owned(), &mut |typ| {
        match **typ {
            Type::Generic(ref generic) => {
                // Replace the generic variable with the type from the list
                // or if it is not found the make a fresh variable
                alias
                    .params()
                    .iter()
                    .zip(&*alias_type.unapplied_args())
                    .find(|&(arg, _)| arg.id == generic.id)
                    .map(|(_, typ)| typ.clone())
            }
            _ => None,
        }
    });

    get_return_type(env, &typ, arg_count)
}

pub fn is_operator_char(c: char) -> bool {
    "!#$%&*+-./<=>?@\\^|-~:".chars().any(|x| x == c)
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
        _ => return Err("Expected a string literal or path to import"),
    }
}
