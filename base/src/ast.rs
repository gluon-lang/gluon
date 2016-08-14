//! Module containing the types which make up `gluon`'s AST (Abstract Syntax Tree)
use std::cmp::Ordering;
use std::fmt;
use std::ops::Deref;

use pos::{BytePos, CharPos};
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

/// Representation of a location in a source file
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct Location {
    pub row: u32,
    pub column: CharPos,
    pub absolute: BytePos,
}

impl Location {
    fn line_offset(mut self, offset: CharPos) -> Location {
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

impl Span {
    pub fn containment(&self, location: &Location) -> Ordering {
        use std::cmp::Ordering::*;
        match (location.cmp(&self.start), location.cmp(&self.end)) {
            (Equal, _) | (Greater, Less) => Equal,
            (Less, _) => Less,
            (_, Equal) | (_, Greater) => Greater,
        }
    }
    pub fn containment_exclusive(&self, location: &Location) -> Ordering {
        if self.end == *location {
            Ordering::Greater
        } else {
            self.containment(location)
        }
    }
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

#[derive(Clone, PartialEq, Debug)]
pub enum LiteralEnum {
    Byte(u8),
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
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
        types: Vec<(Id::Untyped, Option<AstType<Id::Untyped>>)>,
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
    pub alias: Alias<Id, AstType<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding<Id: AstId> {
    pub comment: Option<String>,
    pub name: LPattern<Id>,
    pub typ: Option<AstType<Id::Untyped>>,
    pub arguments: Vec<Id>,
    pub expression: LExpr<Id>,
}

impl<Id> LExpr<Id>
    where Id: AstId
{
    /// Returns the an approximation of the span of the expression
    pub fn span<'a>(&self, env: &(DisplayEnv<Ident = Id> + 'a)) -> Span {
        use self::Expr::*;
        let end = match self.value {
            Identifier(ref id) => self.location.line_offset(CharPos(env.string(id).len())),
            Literal(ref lit) => {
                use self::LiteralEnum::*;
                match *lit {
                    Integer(i) => self.location.line_offset(CharPos::from(format!("{}", i).len())),
                    Byte(i) => self.location.line_offset(CharPos::from(format!("{}", i).len() + 1)),
                    Float(f) => self.location.line_offset(CharPos::from(format!("{}", f).len())),
                    String(ref s) => self.location.line_offset(CharPos::from(s.len() + 2)),
                    Char(_) => self.location.line_offset(CharPos(3)),
                }
            }
            Call(ref func, ref args) => {
                args.last()
                    .map_or_else(|| func.span(env).end, |e| e.span(env).end)
            }
            IfElse(_, ref if_true, ref if_false) => {
                if_false.as_ref()
                    .map_or_else(|| if_true.span(env).end, |e| e.span(env).end)
            }
            Match(_, ref alts) => {
                alts.last()
                    .map_or(self.location, |alt| alt.expression.span(env).end)
            }
            BinOp(_, _, ref r) => r.span(env).end,
            Let(_, ref expr) |
            Type(_, ref expr) => expr.span(env).end,
            FieldAccess(ref expr, ref id) => {
                let base = expr.span(env).end;
                base.line_offset(CharPos::from(1 + env.string(id).len()))
            }
            Array(ref array) => {
                array.expressions
                    .last()
                    .map_or(self.location, |expr| expr.span(env).end)
                    .line_offset(CharPos(1))
            }
            Record { ref exprs, .. } => {
                exprs.last()
                    .and_then(|tup| tup.1.as_ref().map(|expr| expr.span(env).end))
                    .unwrap_or(self.location)
                    .line_offset(CharPos(2))
            }
            Lambda(ref lambda) => lambda.body.span(env).end,
            Tuple(ref args) => {
                args.last()
                    .map_or(self.location, |expr| expr.span(env).end)
                    .line_offset(CharPos(2))
            }
            Block(ref exprs) => exprs.last().expect("Expr in block").span(env).end,
        };
        Span {
            start: self.location,
            end: end,
        }
    }
}
impl<Id> LPattern<Id>
    where Id: AstId + AsRef<str>,
          Id::Untyped: AsRef<str>
{
    /// Returns the an approximation of the span of the expression
    pub fn span(&self) -> Span {
        // FIXME Use exact spans instead of approximations
        let end = match self.value {
            Pattern::Constructor(ref id, ref args) => {
                let offset = args.iter().fold(0, |acc, arg| acc + arg.as_ref().len() + " ".len());
                self.location.line_offset(CharPos::from(id.as_ref().len() + offset))
            }
            Pattern::Record { ref fields, ref types, .. } => {
                let field_offset = fields.iter().fold(0, |acc, t| {
                    acc + t.0.as_ref().len() +
                    t.1.as_ref().map(|id| id.as_ref().len()).unwrap_or(0) +
                    ",".len()
                });
                let type_offset = types.iter().fold(0, |acc, t| {
                    acc + t.0.as_ref().len() +
                    t.1.as_ref().map(|id| id.as_ref().len()).unwrap_or(0) +
                    ",".len()
                });
                self.location.line_offset(CharPos::from(field_offset + type_offset + "{".len()))
            }
            Pattern::Identifier(ref id) => self.location.line_offset(CharPos::from(id.as_ref().len())),
        };
        Span {
            start: self.location,
            end: end,
        }
    }
}

/// Visitor trait which walks over expressions calling `visit_*` on all encountered elements. By
/// default the `visit_*` functions just walk the tree. If they are overriden the user will need to
/// call `walk_mut_*` to continue traversing the tree.
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
            if let Some(ref mut if_false) = *if_false {
                v.visit_expr(&mut **if_false);
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
            for arg in args {
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
        Pattern::Identifier(ref mut id) => v.visit_identifier(id),
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
            Expr::Identifier(ref id) |
            Expr::FieldAccess(_, ref id) => id.env_type_of(env),
            Expr::Literal(ref lit) => {
                match *lit {
                    LiteralEnum::Integer(_) => Type::int(),
                    LiteralEnum::Float(_) => Type::float(),
                    LiteralEnum::Byte(_) => Type::byte(),
                    LiteralEnum::String(_) => Type::string(),
                    LiteralEnum::Char(_) => Type::char(),
                }
            }
            Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            Expr::Tuple(ref exprs) => {
                assert!(exprs.is_empty());
                Type::unit()
            }
            Expr::BinOp(_, ref op, _) => {
                if let Type::App(_, ref args) = *op.env_type_of(env) {
                    if let Type::App(_, ref args) = *args[1] {
                        return args[1].clone();
                    }
                }
                panic!("Expected function type in binop");
            }
            Expr::Let(_, ref expr) |
            Expr::Type(_, ref expr) => expr.env_type_of(env),
            Expr::Call(ref func, ref args) => {
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

impl<T: Typed> Typed for Located<T> {
    type Id = T::Id;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<T::Id> {
        self.value.env_type_of(env)
    }
}

impl Typed for Option<Box<Located<Expr<TcIdent<Symbol>>>>> {
    type Id = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Symbol> {
        match *self {
            Some(ref t) => t.env_type_of(env),
            None => Type::unit(),
        }
    }
}
impl Typed for Pattern<TcIdent<Symbol>> {
    type Id = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> AstType<Symbol> {
        // Identifier patterns might be a function so use the identifier's type instead
        match *self {
            Pattern::Identifier(ref name) => name.env_type_of(env),
            Pattern::Record { ref id, .. } => id.env_type_of(env),
            Pattern::Constructor(ref id, ref args) => get_return_type(env, &id.typ, args.len()),
        }
    }
}

impl Typed for Binding<TcIdent<Symbol>> {
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
