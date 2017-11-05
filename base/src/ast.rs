//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

use pos::{self, BytePos, HasSpan, Span, Spanned};
use symbol::Symbol;
use types::{self, Alias, AliasData, ArcType, Type, TypeEnv};

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

#[derive(Clone, PartialEq, Debug)]
pub enum Literal {
    Byte(u8),
    Int(i64),
    Float(f64),
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
    Constructor(TypedIdent<Id>, Vec<SpannedPattern<Id>>),
    Record {
        typ: ArcType<Id>,
        types: Vec<PatternField<Id, Id>>,
        fields: Vec<PatternField<Id, SpannedPattern<Id>>>,
    },
    Tuple {
        typ: ArcType<Id>,
        elems: Vec<SpannedPattern<Id>>,
    },
    Ident(TypedIdent<Id>),
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
    pub args: Vec<SpannedIdent<Id>>,
    pub body: Box<SpannedExpr<Id>>,
}

pub type SpannedExpr<Id> = Spanned<Expr<Id>, BytePos>;

pub type SpannedIdent<Id> = Spanned<TypedIdent<Id>, BytePos>;

#[derive(Clone, PartialEq, Debug)]
pub struct ExprField<Id, E> {
    pub comment: Option<Comment>,
    pub name: Spanned<Id, BytePos>,
    pub value: Option<E>,
}

/// The representation of gluon's expression syntax
#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id> {
    /// Identifiers
    Ident(TypedIdent<Id>),
    /// Literal values
    Literal(Literal),
    /// Function application, eg. `f x`
    App(Box<SpannedExpr<Id>>, Vec<SpannedExpr<Id>>),
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
    Infix(Box<SpannedExpr<Id>>, SpannedIdent<Id>, Box<SpannedExpr<Id>>),
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
    /// An invalid expression
    Error,
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub comment: Option<Comment>,
    pub name: Spanned<Id, BytePos>,
    pub alias: Spanned<AliasData<Id, AstType<Id>>, BytePos>,
    pub finalized_alias: Option<Alias<Id, ArcType<Id>>>,
}

impl<Id> TypeBinding<Id> {
    pub fn span(&self) -> Span<BytePos> {
        Span::new(self.name.span.start, self.alias.span.end)
    }
}


#[derive(Clone, PartialEq, Debug)]
pub struct ValueBinding<Id> {
    pub comment: Option<Comment>,
    pub name: SpannedPattern<Id>,
    pub typ: Option<AstType<Id>>,
    pub resolved_type: ArcType<Id>,
    pub args: Vec<SpannedIdent<Id>>,
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
pub trait MutVisitor {
    type Ident;

    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
        walk_mut_expr(self, e);
    }

    fn visit_pattern(&mut self, e: &mut SpannedPattern<Self::Ident>) {
        walk_mut_pattern(self, &mut e.value);
    }

    fn visit_ident(&mut self, id: &mut TypedIdent<Self::Ident>) {
        self.visit_typ(&mut id.typ)
    }
    fn visit_typ(&mut self, _: &mut ArcType<Self::Ident>) {}
}

pub fn walk_mut_expr<V: ?Sized + MutVisitor>(v: &mut V, e: &mut SpannedExpr<V::Ident>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(pred);
            v.visit_expr(if_true);
            v.visit_expr(if_false);
        }
        Expr::Infix(ref mut lhs, ref mut id, ref mut rhs) => {
            v.visit_expr(lhs);
            v.visit_ident(&mut id.value);
            v.visit_expr(rhs);
        }
        Expr::LetBindings(ref mut bindings, ref mut body) => {
            for bind in bindings {
                v.visit_pattern(&mut bind.name);
                for arg in &mut bind.args {
                    v.visit_ident(&mut arg.value);
                }
                v.visit_typ(&mut bind.resolved_type);
                v.visit_expr(&mut bind.expr);
            }
            v.visit_expr(body);
        }
        Expr::App(ref mut func, ref mut args) => {
            v.visit_expr(func);
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
            ref mut exprs,
            ref mut base,
            ..
        } => {
            v.visit_typ(typ);
            for field in exprs {
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
        Expr::Lambda(ref mut lambda) => {
            v.visit_ident(&mut lambda.id);
            for arg in &mut lambda.args {
                v.visit_ident(&mut arg.value);
            }
            v.visit_expr(&mut lambda.body);
        }
        Expr::TypeBindings(_, ref mut expr) => v.visit_expr(expr),
        Expr::Ident(ref mut id) => v.visit_ident(id),
        Expr::Literal(..) | Expr::Error => (),
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_mut_pattern<V: ?Sized + MutVisitor>(v: &mut V, p: &mut Pattern<V::Ident>) {
    match *p {
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
        Pattern::Error => (),
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
        Expr::Infix(ref lhs, ref id, ref rhs) => {
            v.visit_expr(lhs);
            v.visit_typ(&id.value.typ);
            v.visit_expr(rhs);
        }
        Expr::LetBindings(ref bindings, ref body) => {
            for bind in bindings {
                v.visit_pattern(&bind.name);
                v.visit_expr(&bind.expr);
            }
            v.visit_expr(body);
        }
        Expr::App(ref func, ref args) => {
            v.visit_expr(func);
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
        } |
        Expr::Block(ref exprs) => for expr in exprs {
            v.visit_expr(expr);
        },
        Expr::Lambda(ref lambda) => {
            v.visit_typ(&lambda.id.typ);
            v.visit_expr(&lambda.body);
        }
        Expr::TypeBindings(_, ref expr) => v.visit_expr(expr),
        Expr::Ident(ref id) => v.visit_typ(&id.typ),
        Expr::Literal(..) | Expr::Error => (),
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_pattern<'a, V: ?Sized + Visitor<'a>>(v: &mut V, p: &'a Pattern<V::Ident>) {
    match *p {
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
        Pattern::Error => (),
    }
}

/// Trait which abstracts over things that have a type.
/// It is not guaranteed that the correct type is returned until after typechecking
pub trait Typed {
    type Ident;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType<Self::Ident>;
}

impl<Id: Clone> Typed for TypedIdent<Id> {
    type Ident = Id;

    fn env_type_of(&self, _: &TypeEnv) -> ArcType<Id> {
        self.typ.clone()
    }
}

impl Typed for Literal {
    type Ident = Symbol;

    fn env_type_of(&self, _: &TypeEnv) -> ArcType {
        match *self {
            Literal::Int(_) => Type::int(),
            Literal::Float(_) => Type::float(),
            Literal::Byte(_) => Type::byte(),
            Literal::String(_) => Type::string(),
            Literal::Char(_) => Type::char(),
        }
    }
}

impl Typed for Expr<Symbol> {
    type Ident = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType {
        match *self {
            Expr::Ident(ref id) => id.typ.clone(),
            Expr::Projection(_, _, ref typ) |
            Expr::Record { ref typ, .. } |
            Expr::Tuple { ref typ, .. } => typ.clone(),
            Expr::Literal(ref lit) => lit.env_type_of(env),
            Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            Expr::Infix(_, ref op, _) => {
                if let Type::App(_, ref args) = *op.value.typ.clone() {
                    if let Type::App(_, ref args) = *args[1] {
                        return args[1].clone();
                    }
                }
                ice!("Expected function type in binop");
            }
            Expr::LetBindings(_, ref expr) | Expr::TypeBindings(_, ref expr) => {
                expr.env_type_of(env)
            }
            Expr::App(ref func, ref args) => {
                get_return_type(env, &func.env_type_of(env), args.len())
            }
            Expr::Match(_, ref alts) => alts[0].expr.env_type_of(env),
            Expr::Array(ref array) => array.typ.clone(),
            Expr::Lambda(ref lambda) => lambda.id.typ.clone(),
            Expr::Block(ref exprs) => exprs.last().expect("Expr in block").env_type_of(env),
            Expr::Error => Type::hole(),
        }
    }
}

impl<T: Typed> Typed for Spanned<T, BytePos> {
    type Ident = T::Ident;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType<T::Ident> {
        self.value.env_type_of(env)
    }
}

impl Typed for Pattern<Symbol> {
    type Ident = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType {
        // Identifier patterns might be a function so use the identifier's type instead
        match *self {
            Pattern::Ident(ref id) => id.typ.clone(),
            Pattern::Record { ref typ, .. } => typ.clone(),
            Pattern::Tuple { ref typ, .. } => typ.clone(),
            Pattern::Constructor(ref id, ref args) => get_return_type(env, &id.typ, args.len()),
            Pattern::Error => Type::hole(),
        }
    }
}

fn get_return_type(env: &TypeEnv, alias_type: &ArcType, arg_count: usize) -> ArcType {
    // We don't want to panic if we attempt to get the return type of a hole so return a type hole
    // as the return type
    if arg_count == 0 || **alias_type == Type::Hole {
        return alias_type.clone();
    }

    let alias_type = alias_type.remove_forall();
    if let Some((_, ret)) = alias_type.as_function() {
        return get_return_type(env, ret, arg_count - 1);
    }

    let alias = {
        let alias_ident = alias_type.alias_ident().unwrap_or_else(|| {
            ice!(
                "ICE: Expected function with {} more arguments, found {:?}",
                arg_count,
                alias_type
            )
        });

        env.find_type_info(alias_ident).unwrap_or_else(|| {
            ice!("Unexpected type {} is not a function", alias_type)
        })
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
    "#+-*/&|=<>:.".chars().any(|x| x == c)
}

pub fn is_constructor(s: &str) -> bool {
    s.rsplit('.')
        .next()
        .unwrap()
        .starts_with(char::is_uppercase)
}
