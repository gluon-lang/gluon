use interner::{InternedStr};


#[deriving(Clone, Eq, PartialEq, Show)]
pub enum LiteralType {
    StringType,
    IntType,
    FloatType,
    BoolType,
    UnitType
}

#[deriving(Clone, Eq, PartialEq, Show)]
pub enum Type<Id> {
    Type(Id),
    FunctionType(Vec<Type<Id>>, Box<Type<Id>>),
    LiteralType(LiteralType)
}

#[deriving(Clone, PartialEq, Show)]
pub enum Literal {
    Integer(int),
    Float(f64),
    String(InternedStr),
    Bool(bool)
}

#[deriving(Clone, PartialEq, Show)]
pub enum Pattern<Id> {
    ConstructorPattern(Id, Vec<Id>),
    IdentifierPattern(Id)
}

#[deriving(Clone, PartialEq, Show)]
pub struct Alternative<Id> {
    pub pattern: Pattern<Id>,
    pub expression: Expr<Id>
}

#[deriving(Clone, PartialEq, Show)]
pub enum Expr<Id> {
    Identifier(Id),
    Literal(Literal),
    Call(Box<Expr<Id>>, Vec<Expr<Id>>),
    IfElse(Box<Expr<Id>>, Box<Expr<Id>>, Box<Expr<Id>>),
    While(Box<Expr<Id>>, Box<Expr<Id>>),
    Match(Box<Expr<Id>>, Vec<Alternative<Id>>),
    Block(Vec<Expr<Id>>),
    BinOp(Box<Expr<Id>>, Id, Box<Expr<Id>>),
    Let(Id, Box<Expr<Id>>),
    Assign(Box<Expr<Id>>, Box<Expr<Id>>),
    FieldAccess(Box<Expr<Id>>, Id)
}

#[deriving(Clone, PartialEq, Show)]
pub struct Field {
    pub name: InternedStr,
    pub typ: Type<InternedStr>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Function<Id> {
    pub name: Id,
    pub arguments: Vec<Field>,
    pub return_type: Type<InternedStr>,
    pub expression: Expr<Id>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Struct<Id> {
    pub name: Id,
    pub fields: Vec<Field>
}
#[deriving(Clone, PartialEq, Show)]
pub struct Constructor<Id> {
    pub name: Id,
    pub arguments: Vec<Type<InternedStr>>
}
#[deriving(Clone, PartialEq, Show)]
pub struct Enum<Id> {
    pub name: Id,
    pub constructors: Vec<Constructor<Id>>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Module<Id> {
    pub enums: Vec<Enum<Id>>,
    pub functions: Vec<Function<Id>>,
    pub structs: Vec<Struct<Id>>
}

pub static int_type: Type<InternedStr> = LiteralType(IntType);
pub static float_type: Type<InternedStr> = LiteralType(FloatType);
pub static string_type: Type<InternedStr> = LiteralType(StringType);
pub static bool_type: Type<InternedStr> = LiteralType(BoolType);
pub static unit_type: Type<InternedStr> = LiteralType(UnitType);


