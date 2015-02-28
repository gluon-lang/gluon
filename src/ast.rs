use std::ops::Deref;
use std::fmt;
use interner::{InternedStr};
pub use lexer::Location;
pub use self::BuiltinType_::{StringType, IntType, FloatType, BoolType, UnitType};
pub use self::TypeEnum::{Type, TraitType, TypeVariable, Generic, FunctionType, BuiltinType, ArrayType};
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

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType_ {
    StringType,
    IntType,
    FloatType,
    BoolType,
    UnitType
}

impl Copy for BuiltinType_ { }

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum TypeEnum<Id> {
    Type(Id, Vec<TypeEnum<Id>>),
    TraitType(Id, Vec<TypeEnum<Id>>),
    TypeVariable(u32),
    Generic(InternedStr),
    FunctionType(Vec<TypeEnum<Id>>, Box<TypeEnum<Id>>),
    BuiltinType(BuiltinType_),
    ArrayType(Box<TypeEnum<Id>>)
}

pub type VMType = TypeEnum<InternedStr>;

#[derive(Clone, PartialEq, Debug)]
pub enum LiteralStruct {
    Integer(i64),
    Float(f64),
    String(InternedStr),
    Bool(bool)
}

impl Copy for LiteralStruct { }

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
    pub typ: TypeEnum<InternedStr>
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
    Tuple(Vec<TypeEnum<InternedStr>>),
    Record(Vec<Field>)
}

#[derive(Clone, PartialEq, Debug)]
pub struct Constructor<Id> {
    pub name: Id,
    pub arguments: ConstructorType
}

impl ConstructorType {
    pub fn each_type<F>(&self, mut f: F) where F: FnMut(&TypeEnum<InternedStr>) {
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
    pub typ: Constrained<TypeEnum<InternedStr>>,
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
    pub typ: TypeEnum<InternedStr>,
    pub globals: Vec<Global<Id>>
}

#[derive(Clone, PartialEq, Debug)]
pub struct Module<Id> {
    pub datas: Vec<Data<Id>>,
    pub globals: Vec<Global<Id>>,
    pub traits: Vec<Trait<Id>>,
    pub impls: Vec<Impl<Id>>
}

pub static INT_TYPE: VMType = BuiltinType(IntType);
pub static FLOAT_TYPE: VMType = BuiltinType(FloatType);
pub static STRING_TYPE: VMType = BuiltinType(StringType);
pub static BOOL_TYPE: VMType = BuiltinType(BoolType);
pub static UNIT_TYPE: VMType = BuiltinType(UnitType);

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
