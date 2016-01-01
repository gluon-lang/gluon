use std::ops::{Deref, DerefMut};
use std::fmt;
use std::rc::Rc;
use std::string::String as StdString;
use symbol::{Symbols, Symbol};

pub use self::BuiltinType::{StringType, CharType, IntType, FloatType, BoolType, UnitType,
                            FunctionType};
pub use self::LiteralStruct::{Integer, Float, String, Bool};

pub type ASTType<Id> = RcType<Id>;

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

impl AstId for StdString {
    type Untyped = StdString;

    fn to_id(self) -> StdString {
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

pub struct EmptyEnv<T>(::std::marker::PhantomData<T>);

impl<T> EmptyEnv<T> {
    pub fn new() -> EmptyEnv<T> {
        EmptyEnv(::std::marker::PhantomData)
    }
}

impl<T: Deref<Target = str>> DisplayEnv for EmptyEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident
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

impl<T> IdentEnv for EmptyEnv<T> where T: Deref<Target = str> + for<'a> From<&'a str>
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
                kind: Rc::new(Kind::Variable(0)),
            }),
            name: name,
        }
    }
    pub fn id(&self) -> &Id {
        &self.name
    }
}

impl<Id> AsRef<str> for TcIdent<Id> where Id: AsRef<str>
{
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

pub struct TcIdentEnv<Id, Env> {
    pub typ: ASTType<Id>,
    pub env: Env,
}

impl<Id> AstId for TcIdent<Id> where Id: Clone + PartialEq + Eq + fmt::Debug + AstId
{
    type Untyped = Id;

    fn to_id(self) -> Self::Untyped {
        self.name
    }

    fn set_type(&mut self, typ: ASTType<Self::Untyped>) {
        self.typ = typ;
    }
}

impl<Id, Env> DisplayEnv for TcIdentEnv<Id, Env> where Env: DisplayEnv<Ident = Id>
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

#[derive(Copy, Clone, PartialEq, Debug)]
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
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line: {}, Column: {}", self.row, self.column)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Span {
    pub start: Location,
    pub end: Location,
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

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType {
    StringType,
    CharType,
    IntType,
    FloatType,
    BoolType,
    UnitType,
    FunctionType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeConstructor<Id> {
    Data(Id),
    Builtin(BuiltinType),
}

impl<I: fmt::Display> fmt::Display for TypeConstructor<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeConstructor::Data(ref d) => d.fmt(f),
            TypeConstructor::Builtin(b) => b.fmt(f),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Kind {
    Variable(u32),
    Star,
    Function(Rc<Kind>, Rc<Kind>),
}

impl Kind {
    pub fn star() -> Rc<Kind> {
        Rc::new(Kind::Star)
    }
    pub fn function(l: Rc<Kind>, r: Rc<Kind>) -> Rc<Kind> {
        Rc::new(Kind::Function(l, r))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable {
    pub kind: Rc<Kind>,
    pub id: u32,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Generic<Id> {
    pub kind: Rc<Kind>,
    pub id: Id,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type<Id, T = ASTType<Id>> {
    App(T, T),
    Data(TypeConstructor<Id>, Vec<T>),
    Variants(Vec<(Id, T)>),
    Variable(TypeVariable),
    Generic(Generic<Id>),
    Function(Vec<T>, T),
    Builtin(BuiltinType),
    Array(T),
    Record {
        types: Vec<Field<T, T>>,
        fields: Vec<Field<Id, T>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BoxType<Id> {
    typ: Box<Type<Id, BoxType<Id>>>,
}

impl<Id: Deref<Target = str>> fmt::Display for BoxType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id> Deref for BoxType<Id> {
    type Target = Type<Id, BoxType<Id>>;
    fn deref(&self) -> &Type<Id, BoxType<Id>> {
        &self.typ
    }
}
impl<Id> DerefMut for BoxType<Id> {
    fn deref_mut(&mut self) -> &mut Type<Id, BoxType<Id>> {
        &mut self.typ
    }
}

impl<Id> From<Type<Id, BoxType<Id>>> for BoxType<Id> {
    fn from(typ: Type<Id, BoxType<Id>>) -> BoxType<Id> {
        BoxType::new(typ)
    }
}

impl<Id> BoxType<Id> {
    pub fn new(typ: Type<Id, BoxType<Id>>) -> BoxType<Id> {
        BoxType { typ: Box::new(typ) }
    }
    pub fn into_inner(self) -> Type<Id, BoxType<Id>> {
        *self.typ
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RcType<Id> {
    typ: Rc<Type<Id, ASTType<Id>>>,
}

impl<Id: Deref<Target = str>> fmt::Display for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id> Deref for RcType<Id> {
    type Target = Type<Id, RcType<Id>>;
    fn deref(&self) -> &Type<Id, RcType<Id>> {
        &self.typ
    }
}

impl<Id> RcType<Id> {
    pub fn new(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType { typ: Rc::new(typ) }
    }
}

impl<Id: Clone> RcType<Id> {
    pub fn into_inner(self) -> Type<Id, RcType<Id>> {
        (*self.typ).clone()
    }
}

impl<Id> From<Type<Id, RcType<Id>>> for RcType<Id> {
    fn from(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType::new(typ)
    }
}

impl ASTType<Symbol> {
    pub fn clone_strings(&self, symbols: &Symbols) -> ASTType<StdString> {
        self.map(|symbol| StdString::from(symbols.string(symbol)))
    }
}

impl<Id, T> Type<Id, T> where T: Deref<Target = Type<Id, T>>
{
    pub fn map<F, R, T2>(&self, mut f: F) -> T2
        where F: FnMut(&Id) -> R,
              T2: From<Type<R, T2>>
    {
        self.map_(&mut f)
    }

    fn map_<R, T2>(&self, f: &mut FnMut(&Id) -> R) -> T2
        where T2: From<Type<R, T2>>
    {
        let typ = match *self {
            Type::Data(ref ctor, ref args) => {
                let ctor = match *ctor {
                    TypeConstructor::Data(ref id) => TypeConstructor::Data(f(id)),
                    TypeConstructor::Builtin(b) => TypeConstructor::Builtin(b),
                };
                Type::Data(ctor, args.iter().map(|t| t.map_(f)).collect())
            }
            Type::Array(ref inner) => Type::Array(inner.map_(f)),
            Type::Function(ref args, ref ret) => {
                Type::Function(args.iter().map(|t| t.map_(f)).collect(), ret.map_(f))
            }
            Type::Record { ref types, ref fields } => {
                let types = types.iter()
                                 .map(|field| {
                                     Field {
                                         name: field.name.map_(f),
                                         typ: field.typ.map_(f),
                                     }
                                 })
                                 .collect();
                let fields = fields.iter()
                                   .map(|field| {
                                       Field {
                                           name: f(&field.name),
                                           typ: field.typ.map_(f),
                                       }
                                   })
                                   .collect();
                Type::Record {
                    types: types,
                    fields: fields,
                }
            }
            Type::App(ref l, ref r) => Type::App(l.map_(f), r.map_(f)),
            Type::Variants(ref variants) => {
                Type::Variants(variants.iter()
                                       .map(|t| (f(&t.0), t.1.map_(f)))
                                       .collect())
            }
            Type::Builtin(x) => Type::Builtin(x),
            Type::Variable(ref v) => {
                Type::Variable(TypeVariable {
                    kind: v.kind.clone(),
                    id: v.id,
                })
            }
            Type::Generic(ref g) => {
                Type::Generic(Generic {
                    id: f(&g.id),
                    kind: g.kind.clone(),
                })
            }
        };
        T2::from(typ)
    }

    pub fn is_uninitialized(&self) -> bool {
        match *self {
            Type::Variable(ref id) if id.id == 0 => true,
            _ => false,
        }
    }

    pub fn kind(&self) -> Rc<Kind> {
        use self::Type::*;
        match *self {
            App(ref arg, _) => {
                match *arg.kind() {
                    Kind::Function(_, ref ret) => ret.clone(),
                    _ => panic!("Expected function kind"),
                }
            }
            Variable(ref var) => var.kind.clone(),
            Generic(ref gen) => gen.kind.clone(),
            Data(_, _) | Variants(..) | Builtin(_) | Function(_, _) | Array(_) | Record { .. } => {
                Rc::new(Kind::Star)
            }
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum LiteralStruct {
    Integer(i64),
    Float(f64),
    String(StdString),
    Char(char),
    Bool(bool),
}

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id: AstId> {
    Constructor(Id, Vec<Id>),
    Record {
        types: Vec<(Id::Untyped, Option<Id::Untyped>)>,
        fields: Vec<(Id::Untyped, Option<Id::Untyped>)>,
    },
    Identifier(Id),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id: AstId> {
    pub pattern: Pattern<Id>,
    pub expression: LExpr<Id>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ArrayStruct<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<LExpr<Id>>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct LambdaStruct<Id: AstId> {
    // Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub free_vars: Vec<Id>,
    pub arguments: Vec<Id>,
    pub body: Box<LExpr<Id>>,
}

pub type LExpr<Id> = Located<Expr<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id: AstId> {
    Identifier(Id),
    Literal(LiteralStruct),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Vec<Binding<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(ArrayStruct<Id>),
    ArrayAccess(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Record {
        typ: Id,
        types: Vec<(Id::Untyped, Option<ASTType<Id::Untyped>>)>,
        exprs: Vec<(Id::Untyped, Option<LExpr<Id>>)>,
    },
    Lambda(LambdaStruct<Id>),
    Tuple(Vec<LExpr<Id>>),
    Type(Vec<TypeBinding<Id::Untyped>>, Box<LExpr<Id>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct TypeBinding<Id> {
    pub name: ASTType<Id>,
    pub typ: ASTType<Id>,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding<Id: AstId> {
    pub name: Pattern<Id>,
    pub typ: Option<ASTType<Id::Untyped>>,
    pub arguments: Vec<Id>,
    pub expression: LExpr<Id>,
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id, T = ASTType<Id>> {
    pub name: Id,
    pub typ: T,
}

#[derive(Clone, PartialEq, Debug)]
pub enum ConstructorType<Id> {
    Tuple(Vec<ASTType<Id>>),
    Record(Vec<Field<Id>>),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Constructor<Id: AstId> {
    pub name: Id,
    pub arguments: ConstructorType<Id::Untyped>,
}

impl<Id> ConstructorType<Id> {
    pub fn each_type<F>(&self, mut f: F)
        where F: FnMut(&Type<Id>)
    {
        match *self {
            ConstructorType::Tuple(ref args) => {
                for t in args.iter() {
                    f(t);
                }
            }
            ConstructorType::Record(ref fields) => {
                for field in fields.iter() {
                    f(&field.typ);
                }
            }
        }
    }
    pub fn len(&self) -> usize {
        match *self {
            ConstructorType::Tuple(ref args) => args.len(),
            ConstructorType::Record(ref fields) => fields.len(),
        }
    }
}

pub fn str_to_primitive_type(x: &str) -> Option<BuiltinType> {
    let t = match x {
        "Int" => IntType,
        "Float" => FloatType,
        "String" => StringType,
        "Char" => CharType,
        "Bool" => BoolType,
        _ => return None,
    };
    Some(t)
}
pub fn primitive_type_to_str(t: BuiltinType) -> &'static str {
    match t {
        StringType => "String",
        CharType => "Char",
        IntType => "Int",
        FloatType => "Float",
        BoolType => "Bool",
        UnitType => "()",
        FunctionType => "->",
    }
}

pub fn fn_type<I, Id, T>(args: I, return_type: Type<Id, T>) -> Type<Id, T>
    where I: IntoIterator<Item = T>,
          I::IntoIter: DoubleEndedIterator,
          T: From<Type<Id, T>>
{
    args.into_iter()
        .rev()
        .fold(return_type,
              |body, arg| Type::Function(vec![arg], T::from(body)))
}
pub fn type_con<I, T>(s: I, args: Vec<T>) -> Type<I, T>
    where I: Deref<Target = str>
{
    assert!(s.len() != 0);
    let is_var = s.chars().next().unwrap().is_lowercase();
    match str_to_primitive_type(&s) {
        Some(b) => Type::Builtin(b),
        None if is_var => {
            Type::Generic(Generic {
                kind: Rc::new(Kind::Star),
                id: s,
            })
        }
        None => Type::Data(TypeConstructor::Data(s), args),
    }
}

impl<Id> Type<Id, ()> {
    pub fn app(l: ASTType<Id>, r: ASTType<Id>) -> ASTType<Id> {
        ASTType::from(Type::App(l, r))
    }

    pub fn array(typ: ASTType<Id>) -> ASTType<Id> {
        ASTType::from(Type::Array(typ))
    }

    pub fn data(id: TypeConstructor<Id>, args: Vec<ASTType<Id>>) -> ASTType<Id> {
        ASTType::from(Type::Data(id, args))
    }

    pub fn variants(vs: Vec<(Id, ASTType<Id>)>) -> ASTType<Id> {
        ASTType::from(Type::Variants(vs))
    }

    pub fn record(types: Vec<Field<ASTType<Id>, ASTType<Id>>>,
                  fields: Vec<Field<Id>>)
                  -> ASTType<Id> {
        ASTType::from(Type::Record {
            types: types,
            fields: fields,
        })
    }

    pub fn function(args: Vec<ASTType<Id>>, ret: ASTType<Id>) -> ASTType<Id> {
        ASTType::from(args.into_iter()
                          .rev()
                          .fold(ret,
                                |body, arg| ASTType::from(Type::Function(vec![arg], body))))
    }

    pub fn generic(typ: Generic<Id>) -> ASTType<Id> {
        ASTType::from(Type::Generic(typ))
    }

    pub fn builtin(typ: BuiltinType) -> ASTType<Id> {
        ASTType::from(Type::Builtin(typ))
    }

    pub fn variable(typ: TypeVariable) -> ASTType<Id> {
        ASTType::from(Type::Variable(typ))
    }

    pub fn string() -> ASTType<Id> {
        Type::builtin(BuiltinType::StringType)
    }

    pub fn char() -> ASTType<Id> {
        Type::builtin(BuiltinType::CharType)
    }

    pub fn int() -> ASTType<Id> {
        Type::builtin(BuiltinType::IntType)
    }

    pub fn float() -> ASTType<Id> {
        Type::builtin(BuiltinType::FloatType)
    }

    pub fn bool() -> ASTType<Id> {
        Type::builtin(BuiltinType::BoolType)
    }

    pub fn unit() -> ASTType<Id> {
        Type::builtin(BuiltinType::UnitType)
    }
}
impl<Id, T> Type<Id, T> where T: Deref<Target = Type<Id, T>>
{
    ///Returns the inner most application of a type application
    pub fn inner_app(&self) -> &Type<Id, T> {
        match *self {
            Type::App(ref a, _) => a.inner_app(),
            _ => self,
        }
    }
    pub fn level(&self) -> u32 {
        use std::cmp::min;
        fold_type(self,
                  |typ, level| {
                      match *typ {
                          Type::Variable(ref var) => min(var.id, level),
                          _ => level,
                      }
                  },
                  u32::max_value())
    }
}

pub struct ArgIterator<'a, Id: 'a, T: 'a> {
    pub typ: &'a Type<Id, T>,
}

pub fn arg_iter<Id, T>(typ: &Type<Id, T>) -> ArgIterator<Id, T>
    where T: Deref<Target = Type<Id, T>>
{
    ArgIterator { typ: typ }
}

impl<'a, Id, T> Iterator for ArgIterator<'a, Id, T> where T: Deref<Target = Type<Id, T>>
{
    type Item = &'a Type<Id, T>;
    fn next(&mut self) -> Option<&'a Type<Id, T>> {
        match *self.typ {
            Type::Function(ref arg, ref return_type) => {
                self.typ = &**return_type;
                Some(&arg[0])
            }
            _ => None,
        }
    }
}

impl<Id> ASTType<Id> {
    pub fn return_type(&self) -> &ASTType<Id> {
        match **self {
            Type::Function(_, ref return_type) => return_type.return_type(),
            _ => self,
        }
    }
}

impl TypeVariable {
    pub fn new(var: u32) -> TypeVariable {
        TypeVariable::with_kind(Kind::Star, var)
    }
    pub fn with_kind(kind: Kind, var: u32) -> TypeVariable {
        TypeVariable {
            kind: Rc::new(kind),
            id: var,
        }
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Kind::Variable(i) => i.fmt(f),
            Kind::Star => '*'.fmt(f),
            Kind::Function(ref arg, ref ret) => write!(f, "({} -> {})", arg, ret),
        }
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl<Id: fmt::Display> fmt::Display for Generic<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl fmt::Display for BuiltinType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        primitive_type_to_str(*self).fmt(f)
    }
}

fn dt<'a, I, T, E>(env: &'a E, prec: Prec, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    DisplayType {
        env: env,
        prec: prec,
        typ: typ,
    }
}

fn top<'a, I, T, E>(env: &'a E, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    dt(env, Prec::Top, typ)
}

pub fn display_type<'a, I, T, E>(env: &'a E, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    top(env, typ)
}

pub struct DisplayType<'a, I: 'a, T: 'a, E: 'a> {
    prec: Prec,
    typ: &'a Type<I, T>,
    env: &'a E,
}

impl<'a, I, T, E> fmt::Display for DisplayType<'a, I, T, E>
    where E: DisplayEnv<Ident = I> + 'a,
          T: Deref<Target = Type<I, T>> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let p = self.prec;
        match *self.typ {
            Type::Variable(ref var) => write!(f, "{}", var),
            Type::Generic(ref gen) => write!(f, "{}", self.env.string(&gen.id)),
            Type::Function(ref args, ref result) => {
                if p >= Prec::Function {
                    write!(f,
                           "({} -> {})",
                           top(self.env, &*args[0]),
                           top(self.env, &**result))
                } else {
                    write!(f,
                           "{} -> {}",
                           dt(self.env, Prec::Function, &args[0]),
                           top(self.env, &**result))
                }
            }
            Type::App(ref lhs, ref rhs) => {
                if p >= Prec::Constructor {
                    write!(f,
                           "({} {})",
                           dt(self.env, Prec::Function, &lhs),
                           dt(self.env, Prec::Constructor, &rhs))
                } else {
                    write!(f,
                           "{} {}",
                           dt(self.env, Prec::Function, &lhs),
                           dt(self.env, Prec::Constructor, &rhs))
                }
            }
            Type::Data(ref t, ref args) => {
                if p >= Prec::Constructor {
                    try!(write!(f, "("));
                }
                match *t {
                    TypeConstructor::Data(ref d) => try!(write!(f, "{}", self.env.string(d))),
                    TypeConstructor::Builtin(ref b) => try!(write!(f, "{}", b)),
                }
                for arg in args {
                    try!(write!(f, " {}", dt(self.env, Prec::Constructor, arg)));
                }
                if p >= Prec::Constructor {
                    try!(write!(f, ")"));
                }
                Ok(())
            }
            Type::Variants(ref variants) => {
                if p >= Prec::Constructor {
                    try!(write!(f, "("));
                }
                for variant in variants {
                    try!(write!(f, "| {}", self.env.string(&variant.0)));
                    for arg in arg_iter(&variant.1) {
                        try!(write!(f, " {}", dt(self.env, Prec::Constructor, &arg)));
                    }
                }
                if p >= Prec::Constructor {
                    try!(write!(f, ")"));
                }
                Ok(())
            }
            Type::Builtin(ref t) => t.fmt(f),
            Type::Array(ref t) => write!(f, "[{}]", top(self.env, &**t)),
            Type::Record { ref types, ref fields } => {
                try!(write!(f, "{{"));
                if types.len() > 0 {
                    try!(write!(f,
                                " {} = {}",
                                top(self.env, &*types[0].name),
                                top(self.env, &*types[0].typ)));
                    for field in &types[1..] {
                        try!(write!(f,
                                    ", {} = {}",
                                    top(self.env, &*field.name),
                                    top(self.env, &*field.typ)));
                    }
                    if fields.len() == 0 {
                        try!(write!(f, " "));
                    }
                }
                if fields.len() > 0 {
                    if types.len() > 0 {
                        try!(write!(f, ","));
                    }
                    try!(write!(f,
                                " {}: {}",
                                self.env.string(&fields[0].name),
                                top(self.env, &*fields[0].typ)));
                    for field in &fields[1..] {
                        try!(write!(f,
                                    ", {}: {}",
                                    self.env.string(&field.name),
                                    top(self.env, &*field.typ)));
                    }
                    try!(write!(f, " "));
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    Top,
    Function,
    Constructor,
}

impl<I, T> fmt::Display for Type<I, T>
    where I: Deref<Target = str>,
          T: Deref<Target = Type<I, T>>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", dt(&EmptyEnv::new(), Prec::Top, self))
    }
}


pub trait MutVisitor {
    type T: AstId;
    fn visit_expr(&mut self, e: &mut LExpr<Self::T>) {
        walk_mut_expr(self, e);
    }
    fn visit_pattern(&mut self, e: &mut Pattern<Self::T>) {
        walk_mut_pattern(self, e);
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
        Expr::ArrayAccess(ref mut array, ref mut index) => {
            v.visit_expr(&mut **array);
            v.visit_expr(&mut **index);
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
        Pattern::Record { .. } => (),
        Pattern::Identifier(ref mut id) => v.visit_identifier(id),
    }
}

pub fn walk_type<I, T, F>(typ: &Type<I, T>, f: &mut F)
    where F: FnMut(&Type<I, T>),
          T: Deref<Target = Type<I, T>>
{
    f(typ);
    match *typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_type(a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_type(&**inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_type(a, f);
            }
            walk_type(&**ret, f);
        }
        Type::Record { ref types, ref fields } => {
            for field in types {
                walk_type(&field.name, f);
                walk_type(&field.typ, f);
            }
            for field in fields {
                walk_type(&field.typ, f);
            }
        }
        Type::App(ref l, ref r) => {
            walk_type(l, f);
            walk_type(r, f);
        }
        Type::Variants(ref variants) => {
            for variant in variants {
                walk_type(&variant.1, f);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => (),
    }
}

pub fn fold_type<I, T, F, A>(typ: &Type<I, T>, mut f: F, a: A) -> A
    where F: FnMut(&Type<I, T>, A) -> A,
          T: Deref<Target = Type<I, T>>
{
    let mut a = Some(a);
    walk_type(typ,
              &mut |t| {
                  a = Some(f(t, a.take().expect("None in fold_type")));
              });
    a.expect("fold_type")
}

pub fn walk_mut_type<F, I, T>(typ: &mut Type<I, T>, f: &mut F)
    where F: FnMut(&mut Type<I, T>),
          T: DerefMut<Target = Type<I, T>>
{
    walk_mut_type2(typ, f, &mut |_| ())
}
pub fn walk_mut_type2<F, G, I, T>(typ: &mut Type<I, T>, f: &mut F, g: &mut G)
    where F: FnMut(&mut Type<I, T>),
          G: FnMut(&mut Type<I, T>),
          T: DerefMut<Target = Type<I, T>>
{
    f(typ);
    match *typ {
        Type::Data(_, ref mut args) => {
            for a in args {
                walk_mut_type2(a, f, g);
            }
        }
        Type::Array(ref mut inner) => {
            walk_mut_type2(&mut **inner, f, g);
        }
        Type::Function(ref mut args, ref mut ret) => {
            for a in args {
                walk_mut_type2(a, f, g);
            }
            walk_mut_type2(&mut **ret, f, g);
        }
        Type::Record { ref mut types, ref mut fields } => {
            for field in types {
                walk_mut_type2(&mut field.name, f, g);
                walk_mut_type2(&mut field.typ, f, g);
            }
            for field in fields {
                walk_mut_type2(&mut field.typ, f, g);
            }
        }
        Type::App(ref mut l, ref mut r) => {
            walk_mut_type2(l, f, g);
            walk_mut_type2(r, f, g);
        }
        Type::Variants(ref mut variants) => {
            for variant in variants {
                walk_mut_type2(&mut variant.1, f, g);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => (),
    }
    g(typ);
}

pub fn walk_move_type<F, I, T>(typ: T, f: &mut F) -> T
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    walk_move_type2(&typ, f).unwrap_or(typ)
}

///Create a new instance of `R` if one or both values are `Some`
fn merge<F, A, B, R>(a_original: &A, a: Option<A>, b_original: &B, b: Option<B>, f: F) -> Option<R>
    where A: Clone,
          B: Clone,
          F: FnOnce(A, B) -> R
{
    match (a, b) {
        (Some(a), Some(b)) => Some(f(a, b)),
        (Some(a), None) => Some(f(a, b_original.clone())),
        (None, Some(b)) => Some(f(a_original.clone(), b)),
        (None, None) => None,
    }
}

fn walk_move_type2<F, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    let new = f(typ);
    let result = {
        let typ = new.as_ref().map(|t| &**t).unwrap_or(typ);
        match *typ {
            Type::Data(ref id, ref args) => {
                walk_move_types(args.iter(), |t| walk_move_type2(t, f))
                    .map(|args| Type::Data(id.clone(), args))
                    .map(From::from)
            }
            Type::Array(ref inner) => {
                walk_move_type2(&**inner, f)
                    .map(Type::Array)
                    .map(From::from)
            }
            Type::Function(ref args, ref ret) => {
                let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                merge(args, new_args, ret, walk_move_type2(ret, f), Type::Function).map(From::from)
            }
            Type::Record { ref types, ref fields } => {
                let new_types = None;
                let new_fields = walk_move_types(fields.iter(), |field| {
                    walk_move_type2(&field.typ, f).map(|typ| {
                        Field {
                            name: field.name.clone(),
                            typ: typ,
                        }
                    })
                });
                merge(types, new_types, fields, new_fields, |types, fields| {
                    Type::Record {
                        types: types,
                        fields: fields,
                    }
                })
                    .map(From::from)
            }
            Type::App(ref l, ref r) => {
                merge(l,
                      walk_move_type2(l, f),
                      r,
                      walk_move_type2(r, f),
                      Type::App)
                    .map(From::from)
            }
            Type::Variants(ref variants) => {
                walk_move_types(variants.iter(),
                                |v| walk_move_type2(&v.1, f).map(|t| (v.0.clone(), t)))
                    .map(Type::Variants)
                    .map(From::from)
            }
            Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => None,
        }
    };
    result.or(new)
}
fn walk_move_types<'a, I, F, T>(types: I, mut f: F) -> Option<Vec<T>>
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    let mut out = Vec::new();
    walk_move_types2(types, false, &mut out, &mut f);
    if out.len() == 0 {
        None
    } else {
        out.reverse();
        Some(out)
    }
}
fn walk_move_types2<'a, I, F, T>(mut types: I, replaced: bool, output: &mut Vec<T>, f: &mut F)
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    match types.next() {
        Some(typ) => {
            let new = f(typ);
            walk_move_types2(types, replaced || new.is_some(), output, f);
            match new {
                Some(typ) => {
                    output.push(typ);
                }
                None if replaced || output.len() > 0 => {
                    output.push(typ.clone());
                }
                None => (),
            }
        }
        None => (),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn show_record() {
        assert_eq!(format!("{}", Type::<&str, ()>::record(vec![], vec![])),
                   "{}");
        let typ = Type::record(vec![],
                               vec![Field {
                                        name: "x",
                                        typ: Type::int(),
                                    }]);
        assert_eq!(format!("{}", typ), "{ x: Int }");

        let data = |s, a| ASTType::from(type_con(s, a));
        let f = Type::function(vec![data("a", vec![])], Type::string());
        let test = data("Test", vec![data("a", vec![])]);
        let typ = Type::record(vec![Field {
                                        name: test.clone(),
                                        typ: f.clone(),
                                    }],
                               vec![Field {
                                        name: "x",
                                        typ: Type::int(),
                                    }]);
        assert_eq!(format!("{}", typ), "{ Test a = a -> String, x: Int }");
        let typ = Type::record(vec![Field {
                                        name: test.clone(),
                                        typ: f.clone(),
                                    }],
                               vec![Field {
                                        name: "x",
                                        typ: Type::int(),
                                    },
                                    Field {
                                        name: "test",
                                        typ: test.clone(),
                                    }]);
        assert_eq!(format!("{}", typ),
                   "{ Test a = a -> String, x: Int, test: Test a }");
        let typ = Type::record(vec![Field {
                                        name: test.clone(),
                                        typ: f.clone(),
                                    }],
                               vec![]);
        assert_eq!(format!("{}", typ), "{ Test a = a -> String }");
    }
}
