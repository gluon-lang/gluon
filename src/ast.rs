use std::ops::Deref;
use std::fmt;
use interner::{InternedStr};
pub use lexer::Location;
pub use self::BuiltinType::{StringType, IntType, FloatType, BoolType, UnitType};
pub use self::Pattern::{ConstructorPattern, IdentifierPattern};
pub use self::LiteralStruct::{Integer, Float, String, Bool};
pub use self::Expr::{
    Identifier,
    Literal,
    Call,
    IfElse,
    While,
    Match,
    Block,
    BinOp,
    Let,
    Assign,
    FieldAccess,
    Array,
    ArrayAccess,
    Lambda};


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
pub enum Type<Id> {
    Data(Id, Vec<Type<Id>>),
    Trait(Id, Vec<Type<Id>>),
    Variable(u32),
    Generic(InternedStr),
    Function(Vec<Type<Id>>, Box<Type<Id>>),
    Builtin(BuiltinType),
    Array(Box<Type<Id>>)
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
pub enum Pattern<Id> {
    ConstructorPattern(Id, Vec<Id>),
    IdentifierPattern(Id)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Alternative<Id> {
    pub pattern: Pattern<Id>,
    pub expression: LExpr<Id>
}

#[derive(Clone, PartialEq, Debug)]
pub struct ArrayStruct<Id> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<LExpr<Id>>
}

#[derive(Clone, PartialEq, Debug)]
pub struct LambdaStruct<Id> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub free_vars: Vec<Id>,
    pub arguments: Vec<Id>,
    pub body: Box<LExpr<Id>>
}

pub type LExpr<Id> = Located<Expr<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<Id> {
    Identifier(Id),
    Literal(LiteralStruct),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    While(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    Block(Vec<LExpr<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Id, Box<LExpr<Id>>),
    Assign(Box<LExpr<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(ArrayStruct<Id>),
    ArrayAccess(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Lambda(LambdaStruct<Id>)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Field {
    pub name: InternedStr,
    pub typ: Type<InternedStr>
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
pub struct Global<Id> {
    pub declaration: GlobalDeclaration<Id>,
    pub expression: LExpr<Id>
}

#[derive(Clone, PartialEq, Debug)]
pub enum ConstructorType {
    Tuple(Vec<Type<InternedStr>>),
    Record(Vec<Field>)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Constructor<Id> {
    pub name: Id,
    pub arguments: ConstructorType
}

impl ConstructorType {
    pub fn each_type<F>(&self, mut f: F) where F: FnMut(&Type<InternedStr>) {
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

#[derive(Clone, PartialEq, Debug)]
pub struct Data<Id> {
    pub name: Id,
    pub constraints: Vec<InternedStr>,
    pub constructors: Vec<Constructor<Id>>
}
#[derive(Clone, PartialEq, Debug)]
pub struct GlobalDeclaration<Id> {
    pub name: Id,
    pub typ: Constrained<Type<InternedStr>>,
}
#[derive(Clone, PartialEq, Debug)]
pub struct Trait<Id> {
    pub name: Id,
    pub self_variable: InternedStr,
    pub declarations: Vec<GlobalDeclaration<Id>>
}
#[derive(Clone, PartialEq, Debug)]
pub struct Impl<Id> {
    pub trait_name: Id,
    pub constraints: Vec<Constraint>,
    pub typ: Type<InternedStr>,
    pub globals: Vec<Global<Id>>
}

#[derive(Clone, PartialEq, Debug)]
pub struct Module<Id> {
    pub datas: Vec<Data<Id>>,
    pub globals: Vec<Global<Id>>,
    pub traits: Vec<Trait<Id>>,
    pub impls: Vec<Impl<Id>>
}

pub static INT_TYPE: VMType = Type::Builtin(IntType);
pub static FLOAT_TYPE: VMType = Type::Builtin(FloatType);
pub static STRING_TYPE: VMType = Type::Builtin(StringType);
pub static BOOL_TYPE: VMType = Type::Builtin(BoolType);
pub static UNIT_TYPE: VMType = Type::Builtin(UnitType);

pub fn str_to_primitive_type(x: InternedStr) -> Option<VMType> {
    let t = match x.as_slice() {
        "Int" => INT_TYPE.clone(),
        "Float" => FLOAT_TYPE.clone(),
        "String" => STRING_TYPE.clone(),
        "Bool" => BOOL_TYPE.clone(),
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
        fn fmt_type<I>(f: &mut fmt::Formatter, t: &I, args: &[Type<I>]) -> fmt::Result
            where I: fmt::Display {
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
            Type::Data(ref t, ref args) => fmt_type(f, t, &args),
            Type::Trait(ref t, ref args) => {
                try!(write!(f, "$"));
                fmt_type(f, t, &args)
            }
            Type::Variable(ref x) => x.fmt(f),
            Type::Generic(x) => write!(f, "#{}", x),
            Type::Function(ref args, ref return_type) => {
                try!(write!(f, "("));
                for arg in args {
                    try!(write!(f, "{}", arg));
                }
                try!(write!(f, ") -> {}", return_type));
                Ok(())
            }
            Type::Builtin(ref t) => t.fmt(f),
            Type::Array(ref t) => write!(f, "[{}]", t)
        }
    }
}


pub trait MutVisitor {
    type T;
    fn visit_expr(&mut self, e: &mut LExpr< <Self as MutVisitor>::T>) {
        walk_mut_expr(self, e);
    }
}

pub fn walk_mut_expr<T, V: ?Sized + MutVisitor<T=T>>(v: &mut V, e: &mut LExpr<T>) {
    match e.value {
        IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            match *if_false {
                Some(ref mut if_false) => v.visit_expr(&mut **if_false),
                None => ()
            }
        }
        Block(ref mut exprs) => {
            for expr in exprs.iter_mut() {
                v.visit_expr(expr);
            }
        }
        BinOp(ref mut lhs, _, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_expr(&mut **rhs);
        }
        Let(_, ref mut expr) => {
            v.visit_expr(&mut **expr);
        }
        Call(ref mut func, ref mut args) => {
            v.visit_expr(&mut **func);
            for arg in args.iter_mut() {
                v.visit_expr(arg);
            }
        }
        While(ref mut pred, ref mut expr) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **expr);
        }
        Assign(ref mut lhs, ref mut rhs) => {
            v.visit_expr(&mut **lhs);
            v.visit_expr(&mut **rhs);
        }
        FieldAccess(ref mut expr, _) => {
            v.visit_expr(&mut **expr);
        }
        Match(ref mut expr, ref mut alts) => {
            v.visit_expr(&mut**expr);
            for alt in alts.iter_mut() {
                v.visit_expr(&mut alt.expression);
            }
        }
        Array(ref mut a) => {
            for expr in a.expressions.iter_mut() {
                v.visit_expr(expr);
            }
        }
        ArrayAccess(ref mut array, ref mut index) => {
            v.visit_expr(&mut **array);
            v.visit_expr(&mut **index);
        }
        Lambda(ref mut lambda) => v.visit_expr(&mut *lambda.body),
        Literal(..) | Identifier(..) => ()
    }
}


pub fn walk_mut_type<F, I>(typ: &mut Type<I>, f: &mut F)
    where F: FnMut(&mut Type<I>) {
    f(typ);
    match *typ {
        Type::Data(_, ref mut args) => {
            for a in args {
                walk_mut_type(a, f);
            }
        }
        Type::Trait(_, ref mut args) => {
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
        _ => ()
    }
}
