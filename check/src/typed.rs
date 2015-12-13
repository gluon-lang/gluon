use base::ast;
use base::ast::{ASTType, Type};
use base::interner::InternedStr;

use typecheck::{TcType, TypeEnv, TypeInfos, instantiate};

///Trait which abstracts over things that have a type.
///It is not guaranteed that the correct type is returned until after typechecking
pub trait Typed {
    type Id;
    fn type_of(&self) -> ASTType<Self::Id> {
        self.env_type_of(&TypeInfos::new())
    }
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<Self::Id>;
}
impl<Id: Clone> Typed for ast::TcIdent<Id> {
    type Id = Id;
    fn env_type_of(&self, _: &TypeEnv) -> ASTType<Id> {
        self.typ.clone()
    }
}
impl<Id> Typed for ast::Expr<Id>
    where Id: Typed<Id = InternedStr> + AsRef<str> + ast::AstId<Untyped = InternedStr>
{
    type Id = Id::Id;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<InternedStr> {
        match *self {
            ast::Expr::Identifier(ref id) => id.env_type_of(env),
            ast::Expr::Literal(ref lit) => {
                match *lit {
                    ast::Integer(_) => Type::int(),
                    ast::Float(_) => Type::float(),
                    ast::String(_) => Type::string(),
                    ast::Bool(_) => Type::bool(),
                }
            }
            ast::Expr::IfElse(_, ref arm, _) => arm.env_type_of(env),
            ast::Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0);
                Type::unit()
            }
            ast::Expr::BinOp(ref lhs, ref op, _) => {
                match *op.env_type_of(env) {
                    Type::Function(_, ref return_type) => {
                        match **return_type {
                            Type::Function(_, ref return_type) => return return_type.clone(),
                            _ => (),
                        }
                    }
                    _ => (),
                }
                match AsRef::<str>::as_ref(op) {
                    "+" | "-" | "*" => lhs.env_type_of(env),
                    "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" => Type::bool(),
                    _ => panic!(),
                }
            }
            ast::Expr::Let(_, ref expr) => expr.env_type_of(env),
            ast::Expr::Call(ref func, ref args) => {
                get_return_type(env, func.env_type_of(env), args.len())
            }
            ast::Expr::Match(_, ref alts) => alts[0].expression.env_type_of(env),
            ast::Expr::FieldAccess(_, ref id) => id.env_type_of(env),
            ast::Expr::Array(ref a) => a.id.env_type_of(env),
            ast::Expr::ArrayAccess(ref array, _) => {
                let typ = array.env_type_of(env);
                match *typ {
                    Type::Array(ref t) => t.clone(),
                    _ => panic!("Not an array type {:?}", typ),
                }
            }
            ast::Expr::Lambda(ref lambda) => lambda.id.env_type_of(env),
            ast::Expr::Type(_, ref expr) => expr.env_type_of(env),
            ast::Expr::Record { ref typ,  .. } => typ.env_type_of(env),
        }
    }
}

impl Typed for Option<Box<ast::Located<ast::Expr<ast::TcIdent<InternedStr>>>>> {
    type Id = InternedStr;
    fn env_type_of(&self, env: &TypeEnv) -> ASTType<InternedStr> {
        match *self {
            Some(ref t) => t.env_type_of(env),
            None => Type::unit(),
        }
    }
}

impl<T> Typed for ast::Binding<T>
    where T: Typed<Id = InternedStr> + ast::AstId<Untyped = InternedStr>
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
                                         .unwrap_or_else(|| panic!("ICE: '{}' does not exist", id));
                    match typ {
                        Some(typ) => (args, typ.clone()),
                        None => panic!("Unexpected type {} is not a function", alias_type),
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
                panic!("Expected function with {} more arguments, found {}",
                       arg_count,
                       alias_type)
            }
        }
    }
}
