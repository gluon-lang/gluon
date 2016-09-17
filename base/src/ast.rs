//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)

use std::ops::Deref;

use pos::{BytePos, Spanned};
use symbol::Symbol;
use types::{self, Alias, AliasData, ArcType, Type, TypeEnv};

pub trait DisplayEnv {
    type Ident;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str;
}

pub trait IdentEnv: DisplayEnv {
    fn from_str(&mut self, s: &str) -> Self::Ident;
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
    where Id: AsRef<str>,
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
pub enum Pattern<Id> {
    Constructor(TypedIdent<Id>, Vec<TypedIdent<Id>>),
    Record {
        typ: ArcType<Id>,
        types: Vec<(Id, Option<Id>)>,
        fields: Vec<(Id, Option<Id>)>,
    },
    Ident(TypedIdent<Id>),
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
    pub args: Vec<TypedIdent<Id>>,
    pub body: Box<SpannedExpr<Id>>,
}

/// Expression which contains a location
pub type SpannedExpr<Id> = Spanned<Expr<Id>, BytePos>;

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
    IfElse(Box<SpannedExpr<Id>>, Box<SpannedExpr<Id>>, Box<SpannedExpr<Id>>),
    /// Pattern match expression
    Match(Box<SpannedExpr<Id>>, Vec<Alternative<Id>>),
    /// Infix operator expression eg. `f >> g`
    Infix(Box<SpannedExpr<Id>>, TypedIdent<Id>, Box<SpannedExpr<Id>>),
    /// Record field projection, eg. `value.field`
    Projection(Box<SpannedExpr<Id>>, Id, ArcType<Id>),
    /// Array construction
    Array(Array<Id>),
    /// Record construction
    Record {
        typ: ArcType<Id>,
        types: Vec<(Id, Option<ArcType<Id>>)>,
        exprs: Vec<(Id, Option<SpannedExpr<Id>>)>,
    },
    /// Tuple construction
    Tuple(Vec<SpannedExpr<Id>>),
    /// Declare a series of value bindings
    LetBindings(Vec<ValueBinding<Id>>, Box<SpannedExpr<Id>>),
    /// Declare a series of type aliases
    TypeBindings(Vec<TypeBinding<Id>>, Box<SpannedExpr<Id>>),
    /// A group of sequenced expressions
    Block(Vec<SpannedExpr<Id>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub comment: Option<String>,
    pub name: Id,
    pub alias: Alias<Id, ArcType<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueBinding<Id> {
    pub comment: Option<String>,
    pub name: SpannedPattern<Id>,
    pub typ: ArcType<Id>,
    pub args: Vec<TypedIdent<Id>>,
    pub expr: SpannedExpr<Id>,
}

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overriden the user will need to
/// call `walk_mut_*` to continue traversing the tree.
pub trait MutVisitor {
    type Ident;

    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
        walk_mut_expr(self, e);
    }

    fn visit_pattern(&mut self, e: &mut SpannedPattern<Self::Ident>) {
        walk_mut_pattern(self, &mut e.value);
    }

    fn visit_typ(&mut self, _: &mut ArcType<Self::Ident>) {}
}

pub fn walk_mut_expr<V: ?Sized + MutVisitor>(v: &mut V, e: &mut SpannedExpr<V::Ident>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            v.visit_expr(&mut **if_false);
        }
        Expr::Infix(ref mut lhs, ref mut id, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_typ(&mut id.typ);
            v.visit_expr(&mut **rhs);
        }
        Expr::LetBindings(ref mut bindings, ref mut body) => {
            for bind in bindings {
                v.visit_pattern(&mut bind.name);
                v.visit_expr(&mut bind.expr);
                v.visit_typ(&mut bind.typ);
            }
            v.visit_expr(&mut **body);
        }
        Expr::App(ref mut func, ref mut args) => {
            v.visit_expr(&mut **func);
            for arg in args {
                v.visit_expr(arg);
            }
        }
        Expr::Projection(ref mut expr, _, ref mut typ) => {
            v.visit_expr(&mut **expr);
            v.visit_typ(typ);
        }
        Expr::Match(ref mut expr, ref mut alts) => {
            v.visit_expr(&mut **expr);
            for alt in alts.iter_mut() {
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
        Expr::Record { ref mut typ, ref mut exprs, .. } => {
            v.visit_typ(typ);
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
            v.visit_typ(&mut lambda.id.typ);
            v.visit_expr(&mut *lambda.body);
        }
        Expr::TypeBindings(_, ref mut expr) => v.visit_expr(&mut *expr),
        Expr::Ident(ref mut id) => v.visit_typ(&mut id.typ),
        Expr::Literal(..) => (),
        Expr::Block(ref mut exprs) => {
            for expr in exprs {
                v.visit_expr(expr);
            }
        }
    }
}

/// Walks a pattern, calling `visit_*` on all relevant elements
pub fn walk_mut_pattern<V: ?Sized + MutVisitor>(v: &mut V, p: &mut Pattern<V::Ident>) {
    match *p {
        Pattern::Constructor(ref mut id, ref mut args) => {
            v.visit_typ(&mut id.typ);
            for arg in args {
                v.visit_typ(&mut arg.typ);
            }
        }
        Pattern::Record { ref mut typ, .. } => {
            v.visit_typ(typ);
        }
        Pattern::Ident(ref mut id) => v.visit_typ(&mut id.typ),
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

impl Typed for Expr<Symbol> {
    type Ident = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType {
        match *self {
            Expr::Ident(ref id) => id.typ.clone(),
            Expr::Projection(_, _, ref typ) => typ.clone(),
            Expr::Literal(ref lit) => {
                match *lit {
                    Literal::Int(_) => Type::int(),
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
                if let Type::App(_, ref args) = *op.typ.clone() {
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
            Expr::Match(_, ref alts) => alts[0].expr.env_type_of(env),
            Expr::Array(ref array) => array.typ.clone(),
            Expr::Lambda(ref lambda) => lambda.id.typ.clone(),
            Expr::Record { ref typ, .. } => typ.clone(),
            Expr::Block(ref exprs) => exprs.last().expect("Expr in block").env_type_of(env),
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
            Pattern::Constructor(ref id, ref args) => get_return_type(env, &id.typ, args.len()),
        }
    }
}

fn get_return_type(env: &TypeEnv, alias_type: &ArcType, arg_count: usize) -> ArcType {
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

pub fn is_operator_char(c: char) -> bool {
    "+-*/&|=<>".chars().any(|x| x == c)
}
