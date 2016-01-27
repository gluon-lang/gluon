use std::fmt;

use base::ast::{ASTType, Type};
use base::ast;
use base::types::TcType;
use base::symbol::Symbol;

use unify;
use unify::{Error as UnifyError, Unifier, Unifiable, merge};
use instantiate::AliasInstantiator;
use substitution::{Variable, Substitutable};

pub type Error<I> = UnifyError<ASTType<I>, TypeError<I>>;

#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    UndefinedType(I),
    FieldMismatch(I, I),
}

pub fn fmt_error<I>(error: &Error<I>, f: &mut fmt::Formatter) -> fmt::Result
    where I: fmt::Display + ::std::ops::Deref<Target = str>
{
    use unify::Error::*;
    match *error {
        TypeMismatch(ref l, ref r) => {
            write!(f, "Types do not match:\n\tExpected: {}\n\tFound: {}", l, r)
        }
        Other(TypeError::FieldMismatch(ref l, ref r)) => {
            write!(f,
                   "Field names in record do not match.\n\tExpected: {}\n\tFound: {}",
                   l,
                   r)
        }
        Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
        Other(TypeError::UndefinedType(ref id)) => write!(f, "Type `{}` does not exist.", id),
    }
}


pub type UnifierState<'a, 's, U> = unify::UnifierState<'s, AliasInstantiator<'a>, TcType, U>;

impl Variable for ast::TypeVariable {
    fn get_id(&self) -> u32 {
        self.id
    }
}

impl<I> Substitutable for ASTType<I> {
    type Variable = ast::TypeVariable;

    fn new(id: u32) -> ASTType<I> {
        Type::variable(ast::TypeVariable::new(id))
    }

    fn from_variable(var: ast::TypeVariable) -> ASTType<I> {
        Type::variable(var)
    }

    fn get_var(&self) -> Option<&ast::TypeVariable> {
        match **self {
            Type::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn traverse<'s, F>(&'s self, mut f: F)
        where F: FnMut(&'s ASTType<I>) -> &'s ASTType<I>
    {
        walk_type(self, &mut f)
    }
}

impl<'a> Unifiable<AliasInstantiator<'a>> for TcType {
    type Error = TypeError<Symbol>;

    fn zip_match<'s, U>(&self,
                        other: &Self,
                        mut unifier: UnifierState<'a, 's, U>)
                        -> Result<Option<Self>, Error<Symbol>>
        where U: Unifier<AliasInstantiator<'a>, Self>
    {
        debug!("{:?} <=> {:?}", self, other);
        match (&**self, &**other) {
            (&Type::Variable(ref l), &Type::Variable(ref r)) if l.id == r.id => Ok(None),
            (&Type::Function(ref l_args, ref l_ret),
             &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    let args = walk_move_types(l_args.iter().zip(r_args.iter()),
                                               |l, r| unifier.try_match(l, r));
                    let ret = unifier.try_match(l_ret, r_ret);
                    Ok(merge(l_args,
                             args,
                             l_ret,
                             ret,
                             |args, ret| Type::function(args, ret)))
                } else {
                    Err(UnifyError::TypeMismatch(self.clone(), other.clone()))
                }
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::App(..)) => {
                zip_function(&mut unifier, &l_args[0], l_ret, other)
            }
            (&Type::App(..), &Type::Function(ref l_args, ref l_ret)) => {
                zip_function(&mut unifier, &l_args[0], l_ret, self)
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => {
                Ok(unifier.try_match(l, r).map(Type::array))
            }
            (&Type::Data(ref l, ref l_args),
             &Type::Data(ref r, ref r_args))
                if l == r && l_args.len() == r_args.len() => {
                let args = walk_move_types(l_args.iter().zip(r_args.iter()),
                                           |l, r| unifier.try_match(l, r));
                Ok(args.map(|args| Type::data(l.clone(), args)))
            }
            (&Type::Record { fields: ref l_args, types: ref l_types },
             &Type::Record { fields: ref r_args, .. })
                if l_args.len() == r_args.len() => {
                // FIXME Take associated types into account when unifying
                let args = walk_move_types(l_args.iter().zip(r_args.iter()), |l, r| {
                    let opt_type = if l.name != r.name {
                        unifier.report_error(UnifyError::Other(TypeError::FieldMismatch(l.name,
                                                                                        r.name)));
                        Some(unifier.subs.new_var())
                    } else {
                        unifier.try_match(&l.typ, &r.typ)
                    };
                    opt_type.map(|typ| {
                        ast::Field {
                            name: l.name,
                            typ: typ,
                        }
                    })
                });
                Ok(args.map(|args| Type::record(l_types.clone(), args)))
            }
            (&Type::Data(ref l, ref l_args), &Type::App(_, _)) => {
                let result = unifier.match_either(|unifier| {
                                                      unify_app(unifier,
                                                                l,
                                                                l_args,
                                                                other,
                                                                &|unifier, last, r_arg| {
                                                                    unifier.try_match(r_arg, last)
                                                                })
                                                  },
                                                  |unifier| zip_alias(unifier, other, self));
                result.map_err(|()| UnifyError::TypeMismatch(self.clone(), other.clone()))
            }
            (&Type::App(_, _), &Type::Data(ref r, ref r_args)) => {
                let result = unifier.match_either(|unifier| {
                                                      unify_app(unifier,
                                                                r,
                                                                r_args,
                                                                self,
                                                                &|unifier, last, l_arg| {
                                                                    unifier.try_match(l_arg, last)
                                                                })
                                                  },
                                                  |unifier| zip_alias(unifier, self, other));
                result.map_err(|()| UnifyError::TypeMismatch(self.clone(), other.clone()))
            }
            (&Type::App(ref l1, ref l2), &Type::App(ref r1, ref r2)) => {
                let f = unifier.try_match(l1, r1);
                let a = unifier.try_match(l2, r2);
                Ok(merge(l1, f, l2, a, Type::app))
            }
            _ => {
                if self == other {
                    // Successful unification
                    return Ok(None);
                }
                let result = unifier.match_either(|unifier| zip_alias(unifier, self, other),
                                                  |unifier| zip_alias(unifier, other, self));
                result.map_err(|()| UnifyError::TypeMismatch(self.clone(), other.clone()))
            }
        }
    }
}

fn zip_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                        expected: &TcType,
                        actual: &TcType)
                        -> Result<Option<TcType>, ()>
    where U: Unifier<AliasInstantiator<'a>, TcType>
{
    match **actual {
        Type::Data(ast::TypeConstructor::Data(r), ref r_args) => {
            debug!("Attempt alias {:?} {:?}", r, r_args);
            let r = match unifier.state.type_of_alias(r, r_args) {
                Ok(typ) => typ,
                Err(err) => {
                    unifier.report_error(err);
                    return Err(());
                }
            };
            match r {
                Some(r) => {
                    debug!("Found {:?}", r);
                    unifier.try_match(expected, &r);
                    Ok(None)
                }
                None => Err(()),
            }
        }
        _ => Err(()),
    }
}

fn unify_app<'a, 's, F, U>(unifier: &mut UnifierState<'a, 's, U>,
                           l: &ast::TypeConstructor<Symbol>,
                           l_args: &[TcType],
                           r: &TcType,
                           f: &F)
                           -> Result<Option<TcType>, ()>
    where F: Fn(&mut UnifierState<'a, 's, U>, &TcType, &TcType) -> Option<TcType>,
          U: Unifier<AliasInstantiator<'a>, TcType>
{
    let mut args = Vec::new();
    unify_app_(unifier, l, l_args, r, false, &mut args, f);
    if args.is_empty() {
        Ok(None)
    } else {
        Ok(Some(Type::data(l.clone(), args)))
    }
}

fn unify_app_<'a, 's, F, U>(unifier: &mut UnifierState<'a, 's, U>,
                            l: &ast::TypeConstructor<Symbol>,
                            l_args: &[TcType],
                            r: &TcType,
                            replaced: bool,
                            output: &mut Vec<TcType>,
                            f: &F)
    where F: Fn(&mut UnifierState<'a, 's, U>, &TcType, &TcType) -> Option<TcType>,
          U: Unifier<AliasInstantiator<'a>, TcType>
{
    let r = unifier.subs.real(r);
    let new = match **r {
        Type::App(ref r, ref r_arg) => {
            match l_args.last() {
                Some(last) => {
                    let arg_result = f(unifier, last, r_arg);
                    unify_app_(unifier,
                               l,
                               &l_args[0..l_args.len() - 1],
                               r,
                               replaced || arg_result.is_some(),
                               output,
                               f);
                    arg_result
                }
                None => {
                    let l = Type::data(l.clone(), l_args.iter().cloned().collect());
                    unifier.try_match(&l, r)
                }
            }
        }
        Type::Data(ref r, ref r_args) if l == r && l_args.len() == r_args.len() => {
            let args = walk_move_types(l_args.iter().zip(r_args), |l, r| unifier.try_match(l, r));
            match args {
                Some(args) => {
                    output.extend(args);
                    return;
                }
                None => None,
            }
        }
        _ => {
            let l = Type::data(l.clone(), l_args.iter().cloned().collect());
            unifier.try_match(&l, r)
        }
    };
    match new {
        Some(typ) => {
            output.push(typ);
        }
        None if replaced || output.len() > 0 => {
            output.push(r.clone());
        }
        None => (),
    }
}

fn zip_function<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                           arg: &TcType,
                           ret: &TcType,
                           other: &TcType)
                           -> Result<Option<TcType>, Error<Symbol>>
    where U: Unifier<AliasInstantiator<'a>, TcType>
{
    let error = || {
        let func = Type::function(vec![arg.clone()], ret.clone());
        Err(UnifyError::TypeMismatch(func, other.clone()))
    };
    let subs = unifier.subs;
    let other = subs.real(other);
    match **other {
        Type::App(ref other_f, ref other_ret) => {
            let other_f = subs.real(other_f);
            match **other_f {
                Type::App(ref fn_prim, ref other_arg) => {
                    unifier.try_match(fn_prim, &Type::builtin(ast::BuiltinType::FunctionType));
                    let new_arg = unifier.try_match(arg, other_arg);
                    let new_ret = unifier.try_match(ret, other_ret);
                    Ok(merge(arg,
                             new_arg,
                             ret,
                             new_ret,
                             |args, ret| Type::function(vec![args], ret)))
                }
                _ => error(),
            }
        }
        _ => error(),
    }
}

fn walk_type<'s, I>(typ: &'s ASTType<I>, f: &mut FnMut(&'s ASTType<I>) -> &'s ASTType<I>) {
    let typ = f(typ);
    match **typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_type(a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_type(inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_type(a, f);
            }
            walk_type(ret, f);
        }
        Type::Record { ref types, ref fields } => {
            for field in types {
                walk_type(&field.typ.typ, f);
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

fn walk_move_types<'a, I, F, T>(types: I, mut f: F) -> Option<Vec<T>>
    where I: Iterator<Item = (&'a T, &'a T)>,
          F: FnMut(&'a T, &'a T) -> Option<T>,
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
    where I: Iterator<Item = (&'a T, &'a T)>,
          F: FnMut(&'a T, &'a T) -> Option<T>,
          T: Clone + 'a
{
    match types.next() {
        Some((l, r)) => {
            let new = f(l, r);
            walk_move_types2(types, replaced || new.is_some(), output, f);
            match new {
                Some(typ) => {
                    output.push(typ);
                }
                None if replaced || output.len() > 0 => {
                    output.push(l.clone());
                }
                None => (),
            }
        }
        None => (),
    }
}

#[cfg(test)]
mod tests {
    use base::error::Errors;

    use super::TypeError::FieldMismatch;
    use unify::Error::*;
    use unify::unify;
    use instantiate::{AliasInstantiator, Instantiator};
    use base::ast;
    use base::ast::Type;
    use tests::*;


    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::init();
        let (x, y, z, w) = (intern("x"), intern("y"), intern("z"), intern("w"));
        let l = Type::record(vec![],
                             vec![ast::Field {
                                      name: x,
                                      typ: Type::int(),
                                  },
                                  ast::Field {
                                      name: y,
                                      typ: Type::string(),
                                  }]);
        let r = Type::record(vec![],
                             vec![ast::Field {
                                      name: z,
                                      typ: Type::int(),
                                  },
                                  ast::Field {
                                      name: w,
                                      typ: Type::string(),
                                  }]);
        let inst = Instantiator::new();
        let unit = ();
        let mut alias = AliasInstantiator::new(&inst, &unit);
        let result = unify(&inst.subs, &mut alias, &l, &r);
        assert_eq!(result,
                   Err(Errors { errors: vec![Other(FieldMismatch(x, z)), Other(FieldMismatch(y, w))] }));
    }
}
