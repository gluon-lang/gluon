use interner::{InternedStr};
pub use lexer::Location;


#[deriving(Clone, Show)]
pub struct Located<T> {
    pub location: Location,
    pub value: T
}
impl <T: PartialEq> PartialEq for Located<T> {
    fn eq(&self, other: &Located<T>) -> bool {
        self.value == other.value
    }
}
impl <T> Deref<T> for Located<T> {
    fn deref(&self) -> &T {
        &self.value
    }
}

pub fn no_loc<T>(x: T) -> Located<T> {
    Located { location: Location::eof(), value: x }
}

#[deriving(Clone, Eq, PartialEq, Show, Hash)]
pub enum BuiltinType {
    StringType,
    IntType,
    FloatType,
    BoolType,
    UnitType
}
#[deriving(Clone, Eq, PartialEq, Hash)]
pub enum Type<Id> {
    Type(Id, Vec<Type<Id>>),
    TraitType(Id, Vec<Type<Id>>),
    TypeVariable(uint),
    Generic(uint),
    FunctionType(Vec<Type<Id>>, Box<Type<Id>>),
    BuiltinType(BuiltinType),
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
    pub expression: LExpr<Id>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Array<Id> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub expressions: Vec<LExpr<Id>>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Lambda<Id> {
    //Field to store the type of the array since type_of returns a borrowed reference
    pub id: Id,
    pub free_vars: Vec<Id>,
    pub arguments: Vec<Id>,
    pub body: Box<LExpr<Id>>
}

pub type LExpr<Id> = Located<Expr<Id>>;

#[deriving(Clone, PartialEq, Show)]
pub enum Expr<Id> {
    Identifier(Id),
    Literal(Literal),
    Call(Box<LExpr<Id>>, Vec<LExpr<Id>>),
    IfElse(Box<LExpr<Id>>, Box<LExpr<Id>>, Option<Box<LExpr<Id>>>),
    While(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Match(Box<LExpr<Id>>, Vec<Alternative<Id>>),
    Block(Vec<LExpr<Id>>),
    BinOp(Box<LExpr<Id>>, Id, Box<LExpr<Id>>),
    Let(Id, Box<LExpr<Id>>),
    Assign(Box<LExpr<Id>>, Box<LExpr<Id>>),
    FieldAccess(Box<LExpr<Id>>, Id),
    Array(Array<Id>),
    ArrayAccess(Box<LExpr<Id>>, Box<LExpr<Id>>),
    Lambda(Lambda<Id>)
}

#[deriving(Clone, PartialEq, Show)]
pub struct Field {
    pub name: InternedStr,
    pub typ: Type<InternedStr>
}
#[deriving(Clone, PartialEq, Show)]
pub struct Constraints {
    pub type_variable: InternedStr,
    pub constraints: Vec<VMType>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Function<Id> {
    pub declaration: FunctionDeclaration<Id>,
    pub expression: LExpr<Id>
}

#[deriving(Clone, PartialEq, Show)]
pub struct Struct<Id> {
    pub name: Id,
    pub type_variables: Vec<Constraints>,
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
    pub type_variables: Vec<Constraints>,
    pub constructors: Vec<Constructor<Id>>
}
#[deriving(Clone, PartialEq, Show)]
pub struct FunctionDeclaration<Id> {
    pub name: Id,
    pub type_variables: Vec<Constraints>,
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
    pub type_variables: Vec<Constraints>,
    pub typ: Type<InternedStr>,
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

pub static int_type: Type<InternedStr> = BuiltinType(IntType);
pub static float_type: Type<InternedStr> = BuiltinType(FloatType);
pub static string_type: Type<InternedStr> = BuiltinType(StringType);
pub static bool_type: Type<InternedStr> = BuiltinType(BoolType);
pub static unit_type: Type<InternedStr> = BuiltinType(UnitType);


pub fn str_to_primitive_type(x: InternedStr) -> Option<Type<InternedStr>> {
    let t = match x.as_slice() {
        "int" => int_type.clone(),
        "float" => float_type.clone(),
        "string" => string_type.clone(),
        "bool" => bool_type.clone(),
        _ => return None
    };
    Some(t)
}


pub trait MutVisitor<T> {
    fn visit_expr(&mut self, e: &mut LExpr<T>) {
        walk_mut_expr(self, e);
    }
}

pub fn walk_mut_expr<T, V: MutVisitor<T>>(v: &mut V, e: &mut LExpr<T>) {
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
        ArrayAccess(ref mut array, ref mut index) => {
            v.visit_expr(&mut **array);
            v.visit_expr(&mut **index);
        }
        Lambda(ref mut lambda) => v.visit_expr(&mut *lambda.body),
        Literal(..) | Identifier(..) => ()
    }
}
