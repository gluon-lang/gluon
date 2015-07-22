use std::ops::Deref;
use std::fmt;
pub use self::BuiltinType::{StringType, IntType, FloatType, BoolType, UnitType};
pub use self::Pattern::{ConstructorPattern, IdentifierPattern};
pub use self::LiteralStruct::{Integer, Float, String, Bool};

///Trait representing a type that can by used as in identifier in the AST
///Used to allow the AST to both have a representation which has typed expressions etc as well
///as one which only has identifiers (useful for testing)
pub trait AstId {
    type Env = ();
    ///The type used instead of `Self` when the identifier does not need a type
    type Untyped: Clone + PartialEq + Eq + fmt::Debug;
    fn from_str(env: &mut Self::Env, s: &str) -> Self;
    fn to_id(self) -> Self::Untyped;
    fn set_type(&mut self, typ: Type<Self::Untyped>);
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TcIdent<Id> {
    pub typ: Type<Id>,
    pub name: Id
}
impl <Id> TcIdent<Id> {
    pub fn id(&self) -> &Id {
        &self.name
    }
}

impl <Id> AsRef<str> for TcIdent<Id>
    where Id: AsRef<str> {
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

impl <Id> AstId for TcIdent<Id>
    where Id: Clone + PartialEq + Eq + fmt::Debug + AstId {
    type Env = Id::Env;
    type Untyped = Id;
    fn from_str(env: &mut Id::Env, s: &str) -> TcIdent<Id> {
        TcIdent {
            typ: Type::Variable(TypeVariable::with_kind(Kind::Variable(0), 0)),
            name: AstId::from_str(env, s)
        }
    }
    fn to_id(self) -> Id { self.name }
    fn set_type(&mut self, typ: Type<Self::Untyped>) {
        self.typ = typ;
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Location {
    pub column : i32,
    pub row : i32,
    pub absolute : i32
}

impl Location {
    pub fn eof() -> Location {
        Location { column: -1, row: -1, absolute: -1 }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line: {}, Column: {}", self.row, self.column)
    }
}

#[derive(Clone, Debug)]
pub struct Located<T> {
    pub location: Location,
    pub value: T
}
impl <T: PartialEq> PartialEq for Located<T> {
    fn eq(&self, other: &Located<T>) -> bool {
        self.value == other.value
    }
}
impl <T> Deref for Located<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl <T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.location, self.value)
    }
}

pub fn located<T>(location: Location, value: T) -> Located<T> {
    Located { location: location, value: value }
}

pub fn no_loc<T>(x: T) -> Located<T> {
    located(Location::eof(), x)
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType {
    StringType,
    IntType,
    FloatType,
    BoolType,
    UnitType
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeConstructor<Id> {
    Data(Id),
    Builtin(BuiltinType)
}

impl <I: fmt::Display> fmt::Display for TypeConstructor<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeConstructor::Data(ref d) => d.fmt(f),
            TypeConstructor::Builtin(b) => b.fmt(f)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Kind {
    Variable(u32),
    Star,
    Function(Box<Kind>, Box<Kind>)
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable {
    pub kind: Kind,
    pub id: u32
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Generic<Id> {
    pub kind: Kind,
    pub id: Id
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type<Id> {
    App(Box<Type<Id>>, Box<Type<Id>>),
    Data(TypeConstructor<Id>, Vec<Type<Id>>),
    Variants(Vec<(Id, Type<Id>)>),
    Variable(TypeVariable),
    Generic(Generic<Id>),
    Function(Vec<Type<Id>>, Box<Type<Id>>),
    Builtin(BuiltinType),
    Array(Box<Type<Id>>),
    Record(Vec<Field<Id>>)
}

impl <Id> Type<Id> {
    pub fn is_uninitialized(&self) -> bool {
        match *self {
            Type::Variable(ref id) if id.id == 0 => true,
            _ => false
        }
    }
    pub fn kind(&self) -> &Kind {
        use self::Type::*;
        static STAR: Kind = Kind::Star;
        match *self {
            App(ref arg, _) => match *arg.kind() {
                Kind::Function(_, ref ret) => &**ret,
                _ => panic!("Expected function kind")
            },
            Variable(ref var) => &var.kind,
            Generic(ref gen) => &gen.kind,
            Data(_, _) | Variants(..) | Builtin(_) | Function(_, _) | Array(_) | Record(_) => &STAR,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum LiteralStruct<Id> {
    Integer(i64),
    Float(f64),
    String(Id),
    Bool(bool)
}

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id: AstId> {
    ConstructorPattern(Id, Vec<Id>),
    Record(Vec<(Id::Untyped, Option<Id::Untyped>)>),
    IdentifierPattern(Id)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id: AstId> {
    pub pattern: Pattern<Id>,
    pub expression: LExpr<Id>
}

#[derive(Clone, PartialEq, Debug)]
pub struct ArrayStruct<Id: AstId> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<LExpr<Id>>
}

#[derive(Clone, PartialEq, Debug)]
pub struct LambdaStruct<Id: AstId> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub free_vars: Vec<Id>,
    pub arguments: Vec<Id>,
    pub body: Box<LExpr<Id>>
}

pub type LExpr<Id> = Located<Expr<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id: AstId> {
    Identifier(Id),
    Literal(LiteralStruct<Id::Untyped>),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Vec<Binding<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(ArrayStruct<Id>),
    ArrayAccess(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Record(Id, Vec<(Id::Untyped, Option<LExpr<Id>>)>),
    Lambda(LambdaStruct<Id>),
    Tuple(Vec<LExpr<Id>>),
    Type(Type<Id::Untyped>, Type<Id::Untyped>, Box<LExpr<Id>>)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Binding<Id: AstId> {
    pub name: Id,
    pub arguments: Vec<Id>,
    pub expression: LExpr<Id>
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id> {
    pub name: Id,
    pub typ: Type<Id>
}

#[derive(Clone, PartialEq, Debug)]
pub enum ConstructorType<Id> {
    Tuple(Vec<Type<Id>>),
    Record(Vec<Field<Id>>)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Constructor<Id: AstId> {
    pub name: Id,
    pub arguments: ConstructorType<Id::Untyped>
}

impl <Id> ConstructorType<Id> {
    pub fn each_type<F>(&self, mut f: F) where F: FnMut(&Type<Id>) {
        match *self {
            ConstructorType::Tuple(ref args) => for t in args.iter() { f(t); },
            ConstructorType::Record(ref fields) => for field in fields.iter() { f(&field.typ); }
        }
    }
    pub fn len(&self) -> usize {
        match *self {
            ConstructorType::Tuple(ref args) => args.len(),
            ConstructorType::Record(ref fields) => fields.len()
        }
    }
}

pub fn str_to_primitive_type(x: &str) -> Option<BuiltinType> {
    let t = match x {
        "Int" => IntType,
        "Float" => FloatType,
        "String" => StringType,
        "Bool" => BoolType,
        _ => return None
    };
    Some(t)
}
pub fn primitive_type_to_str(t: BuiltinType) -> &'static str {
    match t {
        StringType => "String",
        IntType => "Int",
        FloatType => "Float",
        BoolType => "Bool",
        UnitType => "()"
    }
}

pub fn fn_type<I, Id>(args: I, return_type: Type<Id>) -> Type<Id>
    where I: IntoIterator<Item=Type<Id>>
        , I::IntoIter: DoubleEndedIterator {
    args.into_iter().rev()
        .fold(return_type, |body, arg| Type::Function(vec![arg], Box::new(body)))
}
pub fn type_con<I>(s: I, args: Vec<Type<I>>) -> Type<I>
    where I: Deref<Target=str> {
    assert!(s.len() != 0);
    let is_var = s.chars().next().unwrap().is_lowercase();
    match str_to_primitive_type(&s) {
        Some(b) => Type::Builtin(b),
        None if is_var => Type::Generic(Generic { kind: Kind::Star, id: s }),
        None => Type::Data(TypeConstructor::Data(s), args)
    }
}

impl <Id> Type<Id> {
    ///Returns the inner most application of a type application
    pub fn inner_app(&self) -> &Type<Id> {
        match *self {
            Type::App(ref a, _) => a.inner_app(),
            _ => self
        }
    }
    pub fn level(&self) -> u32 {
        use std::cmp::min;
        match *self {
            Type::App(ref l , ref r) => min(l.level(), r.level()),
            Type::Data(_, ref types) =>
                types.iter()
                    .map(Type::level)
                    .min()
                    .unwrap_or(u32::max_value()),
            Type::Variants(ref types) =>
                types.iter()
                    .map(|v| v.1.level())
                    .min()
                    .unwrap_or(u32::max_value()),
            Type::Variable(ref var) => var.id,
            Type::Function(ref args, ref r) =>
                min(args.iter()
                    .map(Type::level)
                    .min()
                    .unwrap_or(u32::max_value()), r.level()),
            Type::Array(ref e) => e.level(),
            Type::Record(ref types) => 
                types.iter()
                    .map(|v| v.typ.level())
                    .min()
                    .unwrap_or(u32::max_value()),
            Type::Builtin(_) | Type::Generic(_) => u32::max_value(),
        }
    }

    pub fn return_type(&self) -> &Type<Id> {
        match *self {
            Type::Function(_, ref return_type) => return_type.return_type(),
            _ => self
        }
    }
}

impl TypeVariable {
    pub fn new(var: u32) -> TypeVariable {
        TypeVariable::with_kind(Kind::Star, var)
    }
    pub fn with_kind(kind: Kind, var: u32) -> TypeVariable {
        TypeVariable { kind: kind, id: var  }
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Kind::Variable(i) => i.fmt(f),
            Kind::Star => '*'.fmt(f),
            Kind::Function(ref arg, ref ret) => write!(f, "({} -> {})", arg, ret)
        }
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl <Id: fmt::Display> fmt::Display for Generic<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl fmt::Display for BuiltinType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        primitive_type_to_str(*self).fmt(f)
    }
}

impl <I: fmt::Display> fmt::Display for Type<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn fmt_type<I, T>(f: &mut fmt::Formatter, t: &T, args: &[Type<I>]) -> fmt::Result
            where I: fmt::Display, T: fmt::Display {
            try!(write!(f, "{}", t));
            match args {
                [ref first, rest..] => {
                    try!(write!(f, "<"));
                    try!(write!(f, "{}", first));
                    for arg in rest {
                        try!(write!(f, ", {}", arg));
                    }
                    try!(write!(f, ">"));
                }
                [] => ()
            }
            Ok(())
        }
        match *self {
            Type::App(ref a, ref r) => write!(f, "({} {})", a, r),
            Type::Data(ref t, ref args) => fmt_type(f, t, &args),
            Type::Variants(ref variants) => {
                for variant in variants {
                    try!(write!(f, "| {} {}", variant.0, variant.1));
                }
                Ok(())
            }
            Type::Variable(ref x) => x.fmt(f),
            Type::Generic(ref x) => write!(f, "#{}", x),
            Type::Function(ref args, ref return_type) => {
                try!(write!(f, "("));
                let mut delim = "";
                for arg in args {
                    try!(write!(f, "{}{}", delim, arg));
                    delim = ", ";
                }
                try!(write!(f, ") -> {}", return_type));
                Ok(())
            }
            Type::Builtin(ref t) => t.fmt(f),
            Type::Array(ref t) => write!(f, "[{}]", t),
            Type::Record(ref fields) => {
                try!(write!(f, "{{ "));
                for field in fields {
                    try!(write!(f, " {}: {},", field.name, field.typ));
                }
                write!(f, "}}")
            }
        }
    }
}


pub trait MutVisitor {
    type T: AstId;
    fn visit_expr(&mut self, e: &mut LExpr< <Self as MutVisitor>::T>) {
        walk_mut_expr(self, e);
    }
}

pub fn walk_mut_expr<V: ?Sized + MutVisitor>(v: &mut V, e: &mut LExpr<V::T>) {
    match e.value {
        Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            match *if_false {
                Some(ref mut if_false) => v.visit_expr(&mut **if_false),
                None => ()
            }
        }
        Expr::BinOp(ref mut lhs, _, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_expr(&mut **rhs);
        }
        Expr::Let(ref mut bindings, ref mut body) => {
            for bind in bindings {
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
        Expr::FieldAccess(ref mut expr, _) => {
            v.visit_expr(&mut **expr);
        }
        Expr::Match(ref mut expr, ref mut alts) => {
            v.visit_expr(&mut**expr);
            for alt in alts.iter_mut() {
                v.visit_expr(&mut alt.expression);
            }
        }
        Expr::Array(ref mut a) => {
            for expr in a.expressions.iter_mut() {
                v.visit_expr(expr);
            }
        }
        Expr::ArrayAccess(ref mut array, ref mut index) => {
            v.visit_expr(&mut **array);
            v.visit_expr(&mut **index);
        }
        Expr::Record(_, ref mut fields) => {
            for field in fields {
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
        Expr::Lambda(ref mut lambda) => v.visit_expr(&mut *lambda.body),
        Expr::Type(_, _, ref mut expr) => v.visit_expr(&mut *expr),
        Expr::Literal(..) | Expr::Identifier(..) => ()
    }
}

pub fn walk_type<F, I>(typ: &Type<I>, f: &mut F)
    where F: FnMut(&Type<I>) {
    f(typ);
    match *typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_type(a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_type(& **inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_type(a, f);
            }
            walk_type(& **ret, f);
        }
        Type::Record(ref fields) => {
            for field in fields {
                walk_type(& field.typ, f);
            }
        }
        Type::App(ref l, ref r) => {
            walk_type(l, f);
            walk_type(r, f);
        }
        Type::Variants(ref variants) => {
            for variant in variants {
                walk_type(& variant.1, f);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => ()
    }
}

pub fn walk_mut_type<F, I>(typ: &mut Type<I>, f: &mut F)
    where F: FnMut(&mut Type<I>) {
    walk_mut_type2(typ, f, &mut |_| ())
}
pub fn walk_mut_type2<F, G, I>(typ: &mut Type<I>, f: &mut F, g: &mut G)
    where F: FnMut(&mut Type<I>)
        , G: FnMut(&mut Type<I>) {
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
        Type::Record(ref mut fields) => {
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
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => ()
    }
    g(typ);
}
