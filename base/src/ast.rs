use std::ops::Deref;
use std::fmt;
use interner::{InternedStr};
pub use self::BuiltinType::{StringType, IntType, FloatType, BoolType, UnitType};
pub use self::Pattern::{ConstructorPattern, IdentifierPattern};
pub use self::LiteralStruct::{Integer, Float, String, Bool};

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TcIdent<Id = InternedStr> {
    pub typ: Type<Id>,
    pub name: Id
}
impl <Id> TcIdent<Id> {
    pub fn id(&self) -> &Id {
        &self.name
    }
}

impl AsRef<str> for TcIdent {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

///Trait representing a type that can by used as in identifier in the AST
///Used to allow the AST to both have a representation which has typed expressions etc as well
///as one which only has identifiers (useful for testing)
pub trait AstId {
    ///The type used instead of `Self` when the identifier does not need a type
    type Untyped: Clone + PartialEq + Eq + fmt::Debug;
    fn from_str(s: InternedStr) -> Self;
    fn to_id(self) -> Self::Untyped;
    fn set_type(&mut self, typ: Type<Self::Untyped>);
}

impl AstId for InternedStr {
    type Untyped = InternedStr;
    fn from_str(s: InternedStr) -> InternedStr { s }
    fn to_id(self) -> InternedStr { self }
    fn set_type(&mut self, _: Type<Self::Untyped>) { }
}
impl <Id: Clone + PartialEq + Eq + fmt::Debug + AstId> AstId for TcIdent<Id> {
    type Untyped = Id;
    fn from_str(s: InternedStr) -> TcIdent<Id> { TcIdent { typ: Type::Builtin(UnitType), name: AstId::from_str(s) } }
    fn to_id(self) -> Id { self.name }
    fn set_type(&mut self, typ: Type<Self::Untyped>) {
        self.typ = typ;
    }
}

pub type TcType = Type<InternedStr>;

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
        write!(f, "Line {}, Row {}", self.row, self.column)
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
pub enum Type<Id> {
    App(Box<Type<Id>>, Box<Type<Id>>),
    Data(TypeConstructor<Id>, Vec<Type<Id>>),
    Variable(u32),
    Generic(Id),
    Function(Vec<Type<Id>>, Box<Type<Id>>),
    Builtin(BuiltinType),
    Array(Box<Type<Id>>),
    Record(Vec<Field<Id>>)
}

pub type VMType = Type<InternedStr>;

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum LiteralStruct {
    Integer(i64),
    Float(f64),
    String(InternedStr),
    Bool(bool)
}

#[derive(Clone, PartialEq, Debug)]
pub enum Pattern<Id: AstId> {
    ConstructorPattern(Id, Vec<Id>),
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
    Literal(LiteralStruct),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    While(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    Block(Vec<LExpr<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Id, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    Assign(Box<LExpr<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(ArrayStruct<Id>),
    ArrayAccess(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Record(Id, Vec<(Id::Untyped, LExpr<Id>)>),
    Lambda(LambdaStruct<Id>),
    Type(Id::Untyped, Type<Id::Untyped>, Box<LExpr<Id>>)
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id> {
    pub name: Id,
    pub typ: Type<Id>
}
#[derive(Clone, PartialEq, Debug)]
pub struct Constraint<T = InternedStr> {
    pub name: InternedStr,
    pub type_variable: T,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Constrained<T, I = InternedStr> {
    pub constraints: Vec<Constraint<I>>,
    pub value: T
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

pub static INT_TYPE: VMType = Type::Builtin(IntType);
pub static FLOAT_TYPE: VMType = Type::Builtin(FloatType);
pub static STRING_TYPE: VMType = Type::Builtin(StringType);
pub static BOOL_TYPE: VMType = Type::Builtin(BoolType);
pub static UNIT_TYPE: VMType = Type::Builtin(UnitType);

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
        Expr::Block(ref mut exprs) => {
            for expr in exprs.iter_mut() {
                v.visit_expr(expr);
            }
        }
        Expr::BinOp(ref mut lhs, _, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_expr(&mut **rhs);
        }
        Expr::Let(_, ref mut expr, ref mut body) => {
            v.visit_expr(&mut **expr);
            if let Some(ref mut body) = *body {
                v.visit_expr(&mut **body);
            }
        }
        Expr::Call(ref mut func, ref mut args) => {
            v.visit_expr(&mut **func);
            for arg in args.iter_mut() {
                v.visit_expr(arg);
            }
        }
        Expr::While(ref mut pred, ref mut expr) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **expr);
        }
        Expr::Assign(ref mut lhs, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_expr(&mut **rhs);
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
                v.visit_expr(&mut field.1);
            }
        }
        Expr::Lambda(ref mut lambda) => v.visit_expr(&mut *lambda.body),
        Expr::Type(_, _, ref mut expr) => v.visit_expr(&mut *expr),
        Expr::Literal(..) | Expr::Identifier(..) => ()
    }
}


pub fn walk_mut_type<F, I>(typ: &mut Type<I>, f: &mut F)
    where F: FnMut(&mut Type<I>)
        , I: AstId {
    f(typ);
    match *typ {
        Type::Data(_, ref mut args) => {
            for a in args {
                walk_mut_type(a, f);
            }
        }
        Type::Array(ref mut inner) => {
            walk_mut_type(&mut **inner, f);
        }
        Type::Function(ref mut args, ref mut ret) => {
            for a in args {
                walk_mut_type(a, f);
            }
            walk_mut_type(&mut **ret, f);
        }
        Type::Record(ref mut fields) => {
            for field in fields {
                walk_mut_type(&mut field.typ, f);
            }
        }
        _ => ()
    }
}
