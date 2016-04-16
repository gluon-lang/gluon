//! Module containing the types which make up embed_lang's AST (Abstract Syntax Tree)
use std::fmt;
use std::ops::Deref;
use symbol::Symbol;
use types::{Alias, Type, TypeVariable, TypeConstructor, Kind, TypeEnv, instantiate};

pub type ASTType<Id> = ::types::ArcType<Id>;

///Trait representing a type that can by used as in identifier in the AST
///Used to allow the AST to both have a representation which has typed expressions etc as well
///as one which only has identifiers (useful for testing)
pub trait AstId: Sized {
    ///The type used instead of `Self` when the identifier does not need a type
    type Untyped: Clone + PartialEq + Eq + fmt::Debug;
    fn from_str<E>(env: &mut E, s: &str) -> Self
        where E: IdentEnv<Ident = Self>
    {
        env.from_str(s)
    }
    fn to_id(self) -> Self::Untyped;
    fn set_type(&mut self, typ: ASTType<Self::Untyped>);
}

impl AstId for String {
    type Untyped = String;

    fn to_id(self) -> String {
        self
    }
    fn set_type(&mut self, _typ: ASTType<Self::Untyped>) {}
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
    pub typ: ASTType<Id>,
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
    pub typ: ASTType<Id>,
    pub env: Env,
}

impl<Id> AstId for TcIdent<Id>
    where Id: Clone + PartialEq + Eq + fmt::Debug + AstId
{
    type Untyped = Id;

    fn to_id(self) -> Self::Untyped {
        self.name
    }

    fn set_type(&mut self, typ: ASTType<Self::Untyped>) {
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

/// Representation of a location in a source file
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub struct Location {
    pub column: i32,
    pub row: i32,
    pub absolute: i32,
}

impl Location {
    pub fn eof() -> Location {
        Location {
            column: -1,
            row: -1,
            absolute: -1,
        }
    }

    pub fn line_offset(mut self, offset: i32) -> Location {
        self.column += offset;
        self
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line: {}, Column: {}", self.row, self.column)
    }
}

/// Struct which represents a span in a source file
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Span {
    pub start: Location,
    pub end: Location,
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}

impl<T: fmt::Display> fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.span.start, self.value)
    }
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    pub location: Location,
    pub value: T,
}
impl<T: PartialEq> PartialEq for Located<T> {
    fn eq(&self, other: &Located<T>) -> bool {
        self.value == other.value
    }
}
impl<T> Deref for Located<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.value)
    }
}

pub fn located<T>(location: Location, value: T) -> Located<T> {
    Located {
        location: location,
        value: value,
    }
}

pub fn no_loc<T>(x: T) -> Located<T> {
    located(Location::eof(), x)
}

#[derive(Clone, PartialEq, Debug)]
pub enum LiteralEnum {
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
    Bool(bool),
}

/// Pattern which contains a location
pub type LPattern<Id> = Located<Pattern<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id: AstId> {
    Constructor(Id, Vec<Id>),
    Record {
        id: Id,
        types: Vec<(Id::Untyped, Option<Id::Untyped>)>,
        fields: Vec<(Id::Untyped, Option<Id::Untyped>)>,
    },
    Identifier(Id),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id: AstId> {
    pub pattern: LPattern<Id>,
    pub expression: LExpr<Id>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Array<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<LExpr<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Lambda<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub arguments: Vec<Id>,
    pub body: Box<LExpr<Id>>,
}

/// Expression which contains a location
pub type LExpr<Id> = Located<Expr<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id: AstId> {
    Identifier(Id),
    Literal(LiteralEnum),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Vec<Binding<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(Array<Id>),
    Record {
        typ: Id,
        types: Vec<(Id::Untyped, Option<ASTType<Id::Untyped>>)>,
        exprs: Vec<(Id::Untyped, Option<LExpr<Id>>)>,
    },
    Lambda(Lambda<Id>),
    Tuple(Vec<LExpr<Id>>),
    Type(Vec<TypeBinding<Id::Untyped>>, Box<LExpr<Id>>),
    Block(Vec<LExpr<Id>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub comment: Option<String>,
    pub name: Id,
    pub alias: Alias<Id, ASTType<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding<Id: AstId> {
    pub comment: Option<String>,
    pub name: LPattern<Id>,
    pub typ: Option<ASTType<Id::Untyped>>,
    pub arguments: Vec<Id>,
    pub expression: LExpr<Id>,
}

impl<Id> LExpr<Id>
    where Id: AstId
{
    /// Returns the an approximation of the span of the expression
    pub fn span(&self, env: &DisplayEnv<Ident = Id>) -> Span {
        use self::Expr::*;
        let end = match self.value {
            Identifier(ref id) => self.location.line_offset(env.string(id).len() as i32),
            Literal(ref lit) => {
                use self::LiteralEnum::*;
                match *lit {
                    Integer(i) => self.location.line_offset(format!("{}", i).len() as i32),
                    Float(f) => self.location.line_offset(format!("{}", f).len() as i32),
                    String(ref s) => self.location.line_offset(s.len() as i32 + 2),
                    Char(_) => self.location.line_offset(3),
                    Bool(b) => {
                        self.location.line_offset(if b {
                            4
                        } else {
                            5
                        })
                    }
                }
            }
            Call(ref func, ref args) => {
                args.last()
                    .map(|e| e.span(env).end)
                    .unwrap_or(func.span(env).end)
            }
            IfElse(_, ref if_true, ref if_false) => {
                if_false.as_ref()
                        .map(|e| e.span(env).end)
                        .unwrap_or(if_true.span(env).end)
            }
            Match(_, ref alts) => {
                alts.last()
                    .map(|alt| alt.expression.span(env).end)
                    .unwrap_or(self.location)
            }
            BinOp(_, _, ref r) => r.span(env).end,
            Let(_, ref expr) => expr.span(env).end,
            FieldAccess(ref expr, ref id) => {
                let base = expr.span(env).end;
                base.line_offset(1 + env.string(id).len() as i32)
            }
            Array(ref array) => {
                array.expressions
                     .last()
                     .map(|expr| expr.span(env).end)
                     .unwrap_or(self.location)
                     .line_offset(1)
            }
            Record { ref exprs, .. } => {
                exprs.last()
                     .and_then(|tup| tup.1.as_ref().map(|expr| expr.span(env).end))
                     .unwrap_or(self.location)
                     .line_offset(2)
            }
            Lambda(ref lambda) => lambda.body.span(env).end,
            Tuple(ref args) => {
                args.last()
                    .map(|expr| expr.span(env).end)
                    .unwrap_or(self.location)
                    .line_offset(2)
            }
            Type(_, ref expr) => expr.span(env).end,
            Block(ref exprs) => exprs.last().expect("Expr in block").span(env).end,
        };
        Span {
            start: self.location,
            end: end,
        }
    }
}


pub trait MutVisitor {
    type T: AstId;
    fn visit_expr(&mut self, e: &mut LExpr<Self::T>) {
        walk_mut_expr(self, e);
    }
    fn visit_pattern(&mut self, e: &mut LPattern<Self::T>) {
        walk_mut_pattern(self, &mut e.value);
    }
    fn visit_identifier(&mut self, _: &mut Self::T) {}
}

pub fn walk_mut_expr<V: ?Sized + MutVisitor>(v: &mut V, e: &mut LExpr<V::T>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            match *if_false {
                Some(ref mut if_false) => v.visit_expr(&mut **if_false),
                None => (),
            }
        }
        Expr::BinOp(ref mut lhs, ref mut id, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_identifier(id);
            v.visit_expr(&mut **rhs);
        }
        Expr::Let(ref mut bindings, ref mut body) => {
            for bind in bindings {
                v.visit_pattern(&mut bind.name);
                v.visit_expr(&mut bind.expression);
            }
            v.visit_expr(&mut **body);
        }
        Expr::Call(ref mut func, ref mut args) => {
            v.visit_expr(&mut **func);
            for arg in args.iter_mut() {
                v.visit_expr(arg);
            }
        }
        Expr::FieldAccess(ref mut expr, ref mut id) => {
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
            for expr in a.expressions.iter_mut() {
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
        Expr::Type(_, ref mut expr) => v.visit_expr(&mut *expr),
        Expr::Identifier(ref mut id) => v.visit_identifier(id),
        Expr::Literal(..) => (),
        Expr::Block(ref mut exprs) => {
            for expr in exprs {
                v.visit_expr(expr);
            }
        }
    }
}

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
        Pattern::Identifier(ref mut id) => v.visit_identifier(id),
    }
}

///Trait which abstracts over things that have a type.
///It is not guaranteed that the correct type is returned until after typechecking
pub trait Typed {
    type Id;
    fn type_of(&self) -> ASTType<Self::Id> {
        self.env_type_of(&())
    }
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Self::Id>;
}
impl<Id: Clone> Typed for TcIdent<Id> {
    type Id = Id;
    fn env_type_of(&self, _: &TypeEnv) -> ASTType<Id> {
        self.typ.clone()
    }
}
impl<Id> Typed for Expr<Id>
    where Id: Typed<Id = Symbol> + AstId<Untyped = Symbol>
{
    type Id = Id::Id;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        match *self {
            Expr::Identifier(ref id) => id.env_type_of(env),
            Expr::Literal(ref lit) => {
                match *lit {
                    LiteralEnum::Integer(_) => Type::int(),
                    LiteralEnum::Float(_) => Type::float(),
                    LiteralEnum::String(_) => Type::string(),
                    LiteralEnum::Char(_) => Type::char(),
                    LiteralEnum::Bool(_) => Type::bool(),
                }
            }
            Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0);
                Type::unit()
            }
            Expr::BinOp(_, ref op, _) => {
                match *op.env_type_of(env) {
                    Type::Function(_, ref return_type) => {
                        match **return_type {
                            Type::Function(_, ref return_type) => return return_type.clone(),
                            _ => (),
                        }
                    }
                    _ => (),
                }
                panic!("Expected function type in binop")
            }
            Expr::Let(_, ref expr) => expr.env_type_of(env),
            Expr::Call(ref func, ref args) => {
                get_return_type(env, func.env_type_of(env), args.len())
            }
            Expr::Match(_, ref alts) => alts[0].expression.env_type_of(env),
            Expr::FieldAccess(_, ref id) => id.env_type_of(env),
            Expr::Array(ref a) => a.id.env_type_of(env),
            Expr::Lambda(ref lambda) => lambda.id.env_type_of(env),
            Expr::Type(_, ref expr) => expr.env_type_of(env),
            Expr::Record { ref typ, .. } => typ.env_type_of(env),
            Expr::Block(ref exprs) => exprs.last().expect("Expr in block").env_type_of(env),
        }
    }
}

impl<T: Typed> Typed for Located<T> {
    type Id = T::Id;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<T::Id> {
        self.value.env_type_of(env)
    }
}

impl Typed for Option<Box<Located<Expr<TcIdent<Symbol>>>>> {
    type Id = Symbol;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        match *self {
            Some(ref t) => t.env_type_of(env),
            None => Type::unit(),
        }
    }
}
impl Typed for Pattern<TcIdent<Symbol>> {
    type Id = Symbol;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        // Identifier patterns might be a function so use the identifier's type instead
        match *self {
            Pattern::Identifier(ref name) => name.env_type_of(env),
            Pattern::Record { ref id, .. } => id.env_type_of(env),
            Pattern::Constructor(ref id, ref args) => {
                get_return_type(env, id.typ.clone(), args.len())
            }
        }
    }
}

impl Typed for Binding<TcIdent<Symbol>> {
    type Id = Symbol;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        match self.typ {
            Some(ref typ) => typ.clone(),
            None => self.name.env_type_of(env),
        }
    }
}

fn get_return_type(env: &TypeEnv,
                   alias_type: ASTType<Symbol>,
                   arg_count: usize)
                   -> ASTType<Symbol> {
    if arg_count == 0 {
        alias_type
    } else {
        match *alias_type {
            Type::Function(_, ref ret) => get_return_type(env, ret.clone(), arg_count - 1),
            Type::Data(TypeConstructor::Data(ref id), ref arguments) => {
                let (args, typ) = {
                    let alias = env.find_type_info(&id)
                                   .unwrap_or_else(|| panic!("ICE: '{:?}' does not exist", id));
                    match alias.typ {
                        Some(ref typ) => (&alias.args, typ.clone()),
                        None => panic!("Unexpected type {:?} is not a function", alias_type),
                    }
                };
                let typ = instantiate(typ, |gen| {
                    // Replace the generic variable with the type from the list
                    // or if it is not found the make a fresh variable
                    args.iter()
                        .zip(arguments)
                        .find(|&(arg, _)| arg.id == gen.id)
                        .map(|(_, typ)| typ.clone())
                });
                get_return_type(env, typ, arg_count)

            }
            _ => {
                panic!("Expected function with {} more arguments, found {:?}",
                       arg_count,
                       alias_type)
            }
        }
    }
}
