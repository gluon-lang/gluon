use ast;
use ast::{ASTType, RcKind, Type};
use symbol::Symbol;

pub type TcType = ast::ASTType<Symbol>;
pub type TcIdent = ast::TcIdent<Symbol>;

pub trait KindEnv {
    fn find_kind(&self, type_name: Symbol) -> Option<RcKind>;
}

impl KindEnv for () {
    fn find_kind(&self, _type_name: Symbol) -> Option<RcKind> {
        None
    }
}

impl<'a, T: ?Sized + KindEnv> KindEnv for &'a T {
    fn find_kind(&self, id: Symbol) -> Option<RcKind> {
        (**self).find_kind(id)
    }
}

impl<T: KindEnv, U: KindEnv> KindEnv for (T, U) {
    fn find_kind(&self, id: Symbol) -> Option<RcKind> {
        let &(ref outer, ref inner) = self;
        inner.find_kind(id)
             .or_else(|| outer.find_kind(id))
    }
}

pub trait TypeEnv: KindEnv {
    fn find_type(&self, id: &Symbol) -> Option<&TcType>;
    fn find_type_info(&self, id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)>;
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)>;
}

impl TypeEnv for () {
    fn find_type(&self, _id: &Symbol) -> Option<&TcType> {
        None
    }
    fn find_type_info(&self, _id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        None
    }
    fn find_record(&self, _fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        None
    }
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        (**self).find_type(id)
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        (**self).find_type_info(id)
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        (**self).find_record(fields)
    }
}

impl<T: TypeEnv, U: TypeEnv> TypeEnv for (T, U) {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        let &(ref outer, ref inner) = self;
        inner.find_type(id)
             .or_else(|| outer.find_type(id))
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        let &(ref outer, ref inner) = self;
        inner.find_type_info(id)
             .or_else(|| outer.find_type_info(id))
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        let &(ref outer, ref inner) = self;
        inner.find_record(fields)
             .or_else(|| outer.find_record(fields))
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
impl<Id: Clone> Typed for ast::TcIdent<Id> {
    type Id = Id;
    fn env_type_of(&self, _: &TypeEnv) -> ASTType<Id> {
        self.typ.clone()
    }
}
impl<Id> Typed for ast::Expr<Id> where Id: Typed<Id = Symbol> + ast::AstId<Untyped = Symbol>
{
    type Id = Id::Id;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        match *self {
            ast::Expr::Identifier(ref id) => id.env_type_of(env),
            ast::Expr::Literal(ref lit) => {
                match *lit {
                    ast::LiteralEnum::Integer(_) => Type::int(),
                    ast::LiteralEnum::Float(_) => Type::float(),
                    ast::LiteralEnum::String(_) => Type::string(),
                    ast::LiteralEnum::Char(_) => Type::char(),
                    ast::LiteralEnum::Bool(_) => Type::bool(),
                }
            }
            ast::Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            ast::Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0);
                Type::unit()
            }
            ast::Expr::BinOp(_, ref op, _) => {
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
            ast::Expr::Let(_, ref expr) => expr.env_type_of(env),
            ast::Expr::Call(ref func, ref args) => {
                get_return_type(env, func.env_type_of(env), args.len())
            }
            ast::Expr::Match(_, ref alts) => alts[0].expression.env_type_of(env),
            ast::Expr::FieldAccess(_, ref id) => id.env_type_of(env),
            ast::Expr::Array(ref a) => a.id.env_type_of(env),
            ast::Expr::Lambda(ref lambda) => lambda.id.env_type_of(env),
            ast::Expr::Type(_, ref expr) => expr.env_type_of(env),
            ast::Expr::Record { ref typ,  .. } => typ.env_type_of(env),
        }
    }
}

impl Typed for Option<Box<ast::Located<ast::Expr<ast::TcIdent<Symbol>>>>> {
    type Id = Symbol;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Symbol> {
        match *self {
            Some(ref t) => t.env_type_of(env),
            None => Type::unit(),
        }
    }
}

impl<T> Typed for ast::Binding<T> where T: Typed<Id = Symbol> + ast::AstId<Untyped = Symbol>
{
    type Id = T::Untyped;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<T::Untyped> {
        match self.typ {
            Some(ref typ) => typ.clone(),
            None => {
                match self.name {
                    ast::Pattern::Identifier(ref name) => name.env_type_of(env),
                    _ => panic!("Not implemented"),
                }
            }
        }
    }
}

fn get_return_type(env: &TypeEnv, alias_type: TcType, arg_count: usize) -> TcType {
    if arg_count == 0 {
        alias_type
    } else {
        match *alias_type {
            Type::Function(_, ref ret) => get_return_type(env, ret.clone(), arg_count - 1),
            Type::Data(ast::TypeConstructor::Data(id), ref arguments) => {
                let (args, typ) = {
                    let (args, typ) = env.find_type_info(&id)
                                         .unwrap_or_else(|| {
                                             panic!("ICE: '{:?}' does not exist", id)
                                         });
                    match typ {
                        Some(typ) => (args, typ.clone()),
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

pub fn instantiate<F>(typ: TcType, mut f: F) -> TcType
    where F: FnMut(&ast::Generic<Symbol>) -> Option<TcType>
{
    ast::walk_move_type(typ,
                        &mut |typ| {
                            match *typ {
                                Type::Generic(ref x) => f(x),
                                _ => None,
                            }
                        })
}

