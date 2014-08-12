use interner::{InternedStr};


#[deriving(Clone, Eq, PartialEq, Show, Hash)]
pub enum LiteralType {
    StringType,
    IntType,
    FloatType,
    BoolType,
    UnitType
}

#[deriving(Clone, Eq, PartialEq, Show, Hash)]
pub enum Type<Id> {
    Type(Id),
    FunctionType(Vec<Type<Id>>, Box<Type<Id>>),
    LiteralType(LiteralType),
    ArrayType(Box<Type<Id>>)
}

pub type VMType = Type<InternedStr>;

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
pub struct Array<Id> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<Expr<Id>>
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
    FieldAccess(Box<Expr<Id>>, Id),
    Array(Array<Id>)
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
pub struct FunctionDeclaration<Id> {
    pub name: Id,
    pub arguments: Vec<Field>,
    pub return_type: Type<InternedStr>,
}
#[deriving(Clone, PartialEq, Show)]
pub struct Trait<Id> {
    pub name: Id,
    pub declarations: Vec<FunctionDeclaration<Id>>
}
#[deriving(Clone, PartialEq, Show)]
pub struct Impl<Id> {
    pub trait_name: Id,
    pub type_name: Id,
    pub functions: Vec<Function<Id>>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Module<Id> {
    pub enums: Vec<Enum<Id>>,
    pub functions: Vec<Function<Id>>,
    pub structs: Vec<Struct<Id>>,
    pub traits: Vec<Trait<Id>>,
    pub impls: Vec<Impl<Id>>
}

pub static int_type: Type<InternedStr> = LiteralType(IntType);
pub static float_type: Type<InternedStr> = LiteralType(FloatType);
pub static string_type: Type<InternedStr> = LiteralType(StringType);
pub static bool_type: Type<InternedStr> = LiteralType(BoolType);
pub static unit_type: Type<InternedStr> = LiteralType(UnitType);


pub fn str_to_type(x: InternedStr) -> Type<InternedStr> {
    match x.as_slice() {
        "int" => int_type.clone(),
        "float" => float_type.clone(),
        "string" => string_type.clone(),
        "bool" => bool_type.clone(),
        _ => Type(x)
    }
}


pub trait MutVisitor<T> {
    fn visit_expr(&mut self, e: &mut Expr<T>) {
        walk_mut_expr(self, e);
    }
}

pub fn walk_mut_expr<T, V: MutVisitor<T>>(v: &mut V, e: &mut Expr<T>) {
    match *e {
        IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
            v.visit_expr(&mut **pred);
            v.visit_expr(&mut **if_true);
            v.visit_expr(&mut **if_false);
        }
        Block(ref mut exprs) => {
            for expr in exprs.mut_iter() {
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
            for arg in args.mut_iter() {
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
            for alt in alts.mut_iter() {
                v.visit_expr(&mut alt.expression);
            }
        }
        Array(ref mut a) => {
            for expr in a.expressions.mut_iter() {
                v.visit_expr(expr);
            }
        }
        Literal(..) | Identifier(..) => ()
    }
}
