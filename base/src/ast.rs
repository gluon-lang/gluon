//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)

use std::fmt;
use std::ops::Deref;

use pos::{BytePos, Spanned};
use symbol::Symbol;
use types::{self, Alias, AliasData, Kind, Type, TypeEnv, TypeVariable};

pub type AstType<Id> = ::types::ArcType<Id>;

/// Trait representing a type that can by used as in identifier in the AST
/// Used to allow the AST to both have a representation which has typed expressions etc as well
/// as one which only has identifiers (useful for testing)
pub trait AstId: Sized {
    /// The type used instead of `Self` when the identifier does not need a type
    type Untyped: Clone + PartialEq + Eq + fmt::Debug;
    fn from_str<E>(env: &mut E, s: &str) -> Self
        where E: IdentEnv<Ident = Self>
    {
        env.from_str(s)
    }
    fn to_id(self) -> Self::Untyped;
    fn set_type(&mut self, typ: AstType<Self::Untyped>);
}

impl AstId for String {
    type Untyped = String;

    fn to_id(self) -> String {
        self
    }
    fn set_type(&mut self, _typ: AstType<Self::Untyped>) {}
}

pub trait DisplayEnv {
    type Ident;
    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str;
}

pub trait IdentEnv: DisplayEnv {
    fn from_str(&mut self, s: &str) -> Self::Ident;
}


/// Newtype wrapper which allows `DisplayEnv<Ident = I>` to be used where
/// `DisplayEnv<Ident = TcIdent<Ident = I>` is expected
pub struct TcIdentEnvWrapper<T>(pub T);

impl<I, T: DisplayEnv<Ident = I>> DisplayEnv for TcIdentEnvWrapper<T> {
    type Ident = TcIdent<I>;
    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.0.string(&ident.name)
    }
}

pub struct EmptyEnv<T>(::std::marker::PhantomData<T>);

impl<T> EmptyEnv<T> {
    pub fn new() -> EmptyEnv<T> {
        EmptyEnv(::std::marker::PhantomData)
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

impl<T> IdentEnv for EmptyEnv<T>
    where T: AsRef<str> + for<'a> From<&'a str>
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

impl<'a, T: ?Sized + IdentEnv> IdentEnv for &'a mut T {
    fn from_str(&mut self, s: &str) -> Self::Ident {
        (**self).from_str(s)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TcIdent<Id> {
    pub typ: AstType<Id>,
    pub name: Id,
}
impl<Id> TcIdent<Id> {
    pub fn new(name: Id) -> TcIdent<Id> {
        TcIdent {
            typ: Type::variable(TypeVariable {
                id: 0,
                kind: Kind::variable(0),
            }),
            name: name,
        }
    }
    pub fn id(&self) -> &Id {
        &self.name
    }
}

impl<Id> AsRef<str> for TcIdent<Id>
    where Id: AsRef<str>
{
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

pub struct TcIdentEnv<Id, Env> {
    pub typ: AstType<Id>,
    pub env: Env,
}

impl<Id> AstId for TcIdent<Id>
    where Id: Clone + PartialEq + Eq + fmt::Debug + AstId
{
    type Untyped = Id;

    fn to_id(self) -> Self::Untyped {
        self.name
    }

    fn set_type(&mut self, typ: AstType<Self::Untyped>) {
        self.typ = typ;
    }
}

impl<Id, Env> DisplayEnv for TcIdentEnv<Id, Env>
    where Env: DisplayEnv<Ident = Id>
{
    type Ident = TcIdent<Id>;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.env.string(&ident.name)
    }
}

impl<Id, Env> IdentEnv for TcIdentEnv<Id, Env>
    where Id: Clone,
          Env: IdentEnv<Ident = Id>
{
    fn from_str(&mut self, s: &str) -> TcIdent<Id> {
        TcIdent {
            typ: self.typ.clone(),
            name: self.env.from_str(s),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Literal {
    Byte(u8),
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
}

/// Pattern which contains a location
pub type SpannedPattern<Id> = Spanned<Pattern<Id>, BytePos>;

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id: AstId> {
    Constructor(Id, Vec<Id>),
    Record {
        id: Id,
        types: Vec<(Id::Untyped, Option<Id::Untyped>)>,
        fields: Vec<(Id::Untyped, Option<Id::Untyped>)>,
    },
    Ident(Id),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id: AstId> {
    pub pattern: SpannedPattern<Id>,
    pub expression: SpannedExpr<Id>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Array<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<SpannedExpr<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Lambda<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub arguments: Vec<Id>,
    pub body: Box<SpannedExpr<Id>>,
}

/// Expression which contains a location
pub type SpannedExpr<Id> = Spanned<Expr<Id>, BytePos>;

/// The representation of gluon's expression syntax
#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id: AstId> {
    /// Identifiers
    Ident(Id),
    /// Literal values
    Literal(Literal),
    /// Function application, eg. `f x`
    App(Box<SpannedExpr<Id>>, Vec<SpannedExpr<Id>>),
    /// Lambda abstraction, eg. `\x y -> x * y`
    Lambda(Lambda<Id>),
    /// If-then-else conditional
    IfElse(Box<SpannedExpr<Id>>, Box<SpannedExpr<Id>>, Box<SpannedExpr<Id>>),
    /// Pattern match expression
    Match(Box<SpannedExpr<Id>>, Vec<Alternative<Id>>),
    /// Infix operator expression eg. `f >> g`
    Infix(Box<SpannedExpr<Id>>, Id, Box<SpannedExpr<Id>>),
    /// Record field projection, eg. `value.field`
    Projection(Box<SpannedExpr<Id>>, Id),
    /// Array construction
    Array(Array<Id>),
    /// Record construction
    Record {
        typ: Id,
        types: Vec<(Id::Untyped, Option<AstType<Id::Untyped>>)>,
        exprs: Vec<(Id::Untyped, Option<SpannedExpr<Id>>)>,
    },
    /// Tuple construction
    Tuple(Vec<SpannedExpr<Id>>),
    /// Declare a series of value bindings
    LetBindings(Vec<ValueBinding<Id>>, Box<SpannedExpr<Id>>),
    /// Declare a series of type aliases
    TypeBindings(Vec<TypeBinding<Id::Untyped>>, Box<SpannedExpr<Id>>),
    /// A group of sequenced expressions
    Block(Vec<SpannedExpr<Id>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub comment: Option<String>,
    pub name: Id,
    pub alias: Alias<Id, AstType<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueBinding<Id: AstId> {
    pub comment: Option<String>,
    pub name: SpannedPattern<Id>,
    pub typ: Option<AstType<Id::Untyped>>,
    pub arguments: Vec<Id>,
    pub expression: SpannedExpr<Id>,
}

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overriden the user will need to
/// call `walk_mut_*` to continue traversing the tree.
pub trait MutVisitor {
    type T: AstId;
    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::T>) {
        walk_mut_expr(self, e);
    }
    fn visit_pattern(&mut self, e: &mut SpannedPattern<Self::T>) {
        walk_mut_pattern(self, &mut e.value);
    }
    fn visit_identifier(&mut self, _: &mut Self::T) {}
}

pub fn walk_mut_expr<V: ?Sized + MutVisitor>(v: &mut V, e: &mut SpannedExpr<V::T>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            v.visit_expr(&mut **if_false);
        }
        Expr::Infix(ref mut lhs, ref mut id, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_identifier(id);
            v.visit_expr(&mut **rhs);
        }
        Expr::LetBindings(ref mut bindings, ref mut body) => {
            for bind in bindings {
                v.visit_pattern(&mut bind.name);
                v.visit_expr(&mut bind.expression);
            }
            v.visit_expr(&mut **body);
        }
        Expr::App(ref mut func, ref mut args) => {
            v.visit_expr(&mut **func);
            for arg in args {
                v.visit_expr(arg);
            }
        }
        Expr::Projection(ref mut expr, ref mut id) => {
            v.visit_expr(&mut **expr);
            v.visit_identifier(id);
        }
        Expr::Match(ref mut expr, ref mut alts) => {
            v.visit_expr(&mut **expr);
            for alt in alts.iter_mut() {
                v.visit_pattern(&mut alt.pattern);
                v.visit_expr(&mut alt.expression);
            }
        }
        Expr::Array(ref mut a) => {
            v.visit_identifier(&mut a.id);
            for expr in &mut a.expressions {
                v.visit_expr(expr);
            }
        }
        Expr::Record { ref mut typ, ref mut exprs, .. } => {
            v.visit_identifier(typ);
            for field in exprs {
                if let Some(ref mut expr) = field.1 {
                    v.visit_expr(expr);
                }
            }
        }
        Expr::Tuple(ref mut exprs) => {
            for expr in exprs {
                v.visit_expr(expr);
            }
        }
        Expr::Lambda(ref mut lambda) => {
            v.visit_identifier(&mut lambda.id);
            v.visit_expr(&mut *lambda.body);
        }
        Expr::TypeBindings(_, ref mut expr) => v.visit_expr(&mut *expr),
        Expr::Ident(ref mut id) => v.visit_identifier(id),
        Expr::Literal(..) => (),
        Expr::Block(ref mut exprs) => {
            for expr in exprs {
                v.visit_expr(expr);
            }
        }
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_mut_pattern<V: ?Sized + MutVisitor>(v: &mut V, p: &mut Pattern<V::T>) {
    match *p {
        Pattern::Constructor(ref mut id, ref mut args) => {
            v.visit_identifier(id);
            for a in args {
                v.visit_identifier(a);
            }
        }
        Pattern::Record { ref mut id, .. } => {
            v.visit_identifier(id);
        }
        Pattern::Ident(ref mut id) => v.visit_identifier(id),
    }
}

/// Trait which abstracts over things that have a type.
/// It is not guaranteed that the correct type is returned until after typechecking
pub trait Typed {
    type Id;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Self::Id>;
}

impl<Id: Clone> Typed for TcIdent<Id> {
    type Id = Id;

    fn env_type_of(&self, _: &TypeEnv) -> AstType<Id> {
        self.typ.clone()
    }
}

impl<Id> Typed for Expr<Id>
    where Id: Typed<Id = Symbol> + AstId<Untyped = Symbol>
{
    type Id = Id::Id;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Symbol> {
        match *self {
            Expr::Ident(ref id) |
            Expr::Projection(_, ref id) => id.env_type_of(env),
            Expr::Literal(ref lit) => {
                match *lit {
                    Literal::Integer(_) => Type::int(),
                    Literal::Float(_) => Type::float(),
                    Literal::Byte(_) => Type::byte(),
                    Literal::String(_) => Type::string(),
                    Literal::Char(_) => Type::char(),
                }
            }
            Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            Expr::Tuple(ref exprs) => {
                assert!(exprs.is_empty());
                Type::unit()
            }
            Expr::Infix(_, ref op, _) => {
                if let Type::App(_, ref args) = *op.env_type_of(env) {
                    if let Type::App(_, ref args) = *args[1] {
                        return args[1].clone();
                    }
                }
                panic!("Expected function type in binop");
            }
            Expr::LetBindings(_, ref expr) |
            Expr::TypeBindings(_, ref expr) => expr.env_type_of(env),
            Expr::App(ref func, ref args) => {
                get_return_type(env, &func.env_type_of(env), args.len())
            }
            Expr::Match(_, ref alts) => alts[0].expression.env_type_of(env),
            Expr::Array(ref a) => a.id.env_type_of(env),
            Expr::Lambda(ref lambda) => lambda.id.env_type_of(env),
            Expr::Record { ref typ, .. } => typ.env_type_of(env),
            Expr::Block(ref exprs) => exprs.last().expect("Expr in block").env_type_of(env),
        }
    }
}

impl<T: Typed> Typed for Spanned<T, BytePos> {
    type Id = T::Id;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<T::Id> {
        self.value.env_type_of(env)
    }
}

impl Typed for Pattern<TcIdent<Symbol>> {
    type Id = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Symbol> {
        // Identifier patterns might be a function so use the identifier's type instead
        match *self {
            Pattern::Ident(ref name) => name.env_type_of(env),
            Pattern::Record { ref id, .. } => id.env_type_of(env),
            Pattern::Constructor(ref id, ref args) => get_return_type(env, &id.typ, args.len()),
        }
    }
}

impl Typed for ValueBinding<TcIdent<Symbol>> {
    type Id = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Symbol> {
        match self.typ {
            Some(ref typ) => typ.clone(),
            None => self.name.env_type_of(env),
        }
    }
}

fn get_return_type(env: &TypeEnv,
                   alias_type: &AstType<Symbol>,
                   arg_count: usize)
                   -> AstType<Symbol> {
    if arg_count == 0 {
        alias_type.clone()
    } else {
        match alias_type.as_function() {
            Some((_, ret)) => get_return_type(env, ret, arg_count - 1),
            None => {
                match alias_type.as_alias() {
                    Some((id, alias_args)) => {
                        let (args, typ) = match env.find_type_info(&id).map(Alias::deref) {
                            Some(&AliasData { ref args, typ: Some(ref typ), .. }) => (args, typ),
                            Some(&AliasData { .. }) => panic!("ICE: '{:?}' does not exist", id),
                            None => panic!("Unexpected type {:?} is not a function", alias_type),
                        };

                        let typ = types::instantiate(typ.clone(), |gen| {
                            // Replace the generic variable with the type from the list
                            // or if it is not found the make a fresh variable
                            args.iter()
                                .zip(alias_args)
                                .find(|&(arg, _)| arg.id == gen.id)
                                .map(|(_, typ)| typ.clone())
                        });

                        get_return_type(env, &typ, arg_count)
                    }
                    None => {
                        panic!("ICE: Expected function with {} more arguments, found {:?}",
                               arg_count,
                               alias_type)
                    }
                }
            }
        }
    }
}
