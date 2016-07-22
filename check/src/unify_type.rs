use std::fmt;

use base::types;
use base::types::{Type, merge};
use base::ast::ASTType;
use base::types::{BuiltinType, TcType, TypeVariable, TypeEnv};
use base::symbol::{Symbol, SymbolRef};
use base::instantiate;

use unify;
use unify::{Error as UnifyError, Unifier, Unifiable};
use substitution::{Variable, Substitutable};

pub type Error<I> = UnifyError<ASTType<I>, TypeError<I>>;

#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    UndefinedType(I),
    FieldMismatch(I, I),
}

pub fn fmt_error<I>(error: &Error<I>, f: &mut fmt::Formatter) -> fmt::Result
    where I: fmt::Display + AsRef<str>
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


pub type UnifierState<'a, 's, U> = unify::UnifierState<'s, &'a (TypeEnv + 'a), TcType, U>;

impl Variable for TypeVariable {
    fn get_id(&self) -> u32 {
        self.id
    }
}

impl<I> Substitutable for ASTType<I> {
    type Variable = TypeVariable;

    fn new(id: u32) -> ASTType<I> {
        Type::variable(TypeVariable::new(id))
    }

    fn from_variable(var: TypeVariable) -> ASTType<I> {
        Type::variable(var)
    }

    fn get_var(&self) -> Option<&TypeVariable> {
        match **self {
            Type::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn traverse<'s, F>(&'s self, mut f: F)
        where F: FnMut(&'s ASTType<I>) -> &'s ASTType<I>
    {
        types::walk_type(self, &mut f)
    }
}

impl<'a> Unifiable<&'a (TypeEnv + 'a)> for TcType {
    type Error = TypeError<Symbol>;

    fn zip_match<'s, U>(&self,
                        other: &Self,
                        mut unifier: UnifierState<'a, 's, U>)
                        -> Result<Option<Self>, Error<Symbol>>
        where U: Unifier<&'a (TypeEnv + 'a), Self>
    {
        debug!("{:?} <=> {:?}", self, other);
        let (l_temp, r_temp);
        let (mut l, mut r) = (self, other);
        let mut through_alias = false;
        match try_zip_alias(&mut unifier, self, other, &mut through_alias) {
            Ok((l2, r2)) => {
                l_temp = l2;
                r_temp = r2;
                l = &l_temp;
                r = &r_temp;
            }
            Err(()) => (),
        }
        do_zip_match(l, r, unifier).map(|mut unified_type| {
            // If the match was done through an alias the unified type is likely less precise
            // thean just returning `self` or `None`
            if through_alias {
                unified_type.take();
            }
            unified_type
        })
    }
}

fn do_zip_match<'a, 's, U>(self_: &TcType,
                           other: &TcType,
                           mut unifier: UnifierState<'a, 's, U>)
                           -> Result<Option<TcType>, Error<Symbol>>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    debug!("Unifying:\n{:?} <=> {:?}", self_, other);
    match (&**self_, &**other) {
        (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
            if l_args.len() == r_args.len() {
                let args = walk_move_types(l_args.iter().zip(r_args.iter()),
                                           |l, r| unifier.try_match(l, r));
                let ret = unifier.try_match(l_ret, r_ret);
                Ok(merge(l_args, args, l_ret, ret, Type::function))
            } else {
                debug!("Unify error: {} <=> {}", self_, other);
                Err(UnifyError::TypeMismatch(self_.clone(), other.clone()))
            }
        }
        (&Type::Function(ref l_args, ref l_ret), &Type::App(..)) => {
            zip_function(&mut unifier,
                         &l_args[0],
                         l_ret,
                         other,
                         &mut |u, l, r| u.try_match(l, r))
        }
        (&Type::App(..), &Type::Function(ref l_args, ref l_ret)) => {
            zip_function(&mut unifier,
                         &l_args[0],
                         l_ret,
                         self_,
                         &mut |u, r, l| u.try_match(l, r))
        }
        (&Type::Array(ref l), &Type::Array(ref r)) => Ok(unifier.try_match(l, r).map(Type::array)),
        (&Type::App(ref l, ref l_args), &Type::App(ref r, ref r_args)) => {
            if l_args.len() == r_args.len() {
                let ctor = unifier.try_match(l, r);
                let args = walk_move_types(l_args.iter().zip(r_args.iter()),
                                           |l, r| unifier.try_match(l, r));
                Ok(merge(l, ctor, l_args, args, Type::app))
            } else {
                unify_app(&mut unifier, l, l_args, other)
            }
        }
        (&Type::Record { fields: ref l_args, types: ref l_types },
         &Type::Record { fields: ref r_args, types: ref r_types }) if l_args.len() == r_args.len() &&
                                                                     l_types == r_types => {
            let args = walk_move_types(l_args.iter().zip(r_args.iter()), |l, r| {
                let opt_type = if !l.name.name_eq(&r.name) {

                    let err = TypeError::FieldMismatch(l.name.clone(), r.name.clone());
                    unifier.report_error(UnifyError::Other(err));
                    Some(unifier.subs.new_var())
                } else {
                    unifier.try_match(&l.typ, &r.typ)
                };
                opt_type.map(|typ| {
                    types::Field {
                        name: l.name.clone(),
                        typ: typ,
                    }
                })
            });
            Ok(args.map(|args| Type::record(l_types.clone(), args)))
        }
        (&Type::Id(ref id), &Type::Alias(ref alias)) if *id == alias.name => {
            Ok(Some(other.clone()))
        }
        (&Type::Alias(ref alias), &Type::Id(ref id)) if *id == alias.name => Ok(None),
        _ => {
            if self_ == other {
                // Successful unification
                return Ok(None);
            }
            let result = unifier.match_either(|unifier| try_with_alias(unifier, self_, other),
                                              |unifier| try_with_alias(unifier, other, self_));

            result.map_err(|()| {
                debug!("Unify error: {} <=> {}", self_, other);
                UnifyError::TypeMismatch(self_.clone(), other.clone())
            })
        }
    }
}

// Retrieves the alias name of an application if it exists.
// (Result e Int ==> Result, a -> b ==> ->
fn alias_sym(l: &TcType) -> Option<&SymbolRef> {
    match **l {
        Type::Function(..) => Some(BuiltinType::Function.symbol()),
        _ => l.as_alias().map(|(id, _)| id),
    }
}

/// Attempt to unify two alias types.
/// To find a possible successful unification we go through
fn find_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                         mut l: TcType,
                         r_id: &SymbolRef)
                         -> Result<Option<TcType>, ()>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let mut did_alias = false;
    loop {
        l = match alias_sym(&l) {
            Some(l_id) => {
                debug!("Looking for alias reduction from `{}` to `{}`", l_id, r_id);
                if l_id == r_id {
                    // If the aliases matching bevore going through an alias there is no need to
                    // return a replacement type
                    return Ok(if did_alias {
                        Some(l.clone())
                    } else {
                        None
                    });
                }
                did_alias = true;
                match instantiate::maybe_remove_alias(*unifier.state, &l) {
                    Ok(Some(typ)) => typ,
                    Ok(None) => break,
                    Err(()) => {
                        let l_id = l.as_alias_symbol().unwrap();
                        let err = UnifyError::Other(TypeError::UndefinedType(l_id.clone()));
                        unifier.report_error(err);
                        return Err(());
                    }
                }
            }
            None => break,
        }
    }
    Ok(None)
}

fn try_zip_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                            expected: &TcType,
                            actual: &TcType,
                            through_alias: &mut bool)
                            -> Result<(TcType, TcType), ()>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let mut l = expected.clone();
    if let Some(r_id) = alias_sym(actual) {
        l = match find_alias(unifier, l.clone(), r_id) {
            Ok(None) => l,
            Ok(Some(typ)) => {
                *through_alias = true;
                typ
            }
            Err(()) => expected.clone(),
        };
    }
    let mut r = actual.clone();
    if let Some(l_id) = alias_sym(expected) {
        r = match find_alias(unifier, r.clone(), l_id) {
            Ok(None) => r,
            Ok(Some(typ)) => {
                *through_alias = true;
                typ
            }
            Err(()) => actual.clone(),
        };
    }
    Ok((l, r))
}

fn try_with_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                             expected: &TcType,
                             actual: &TcType)
                             -> Result<Option<TcType>, ()>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let r = match instantiate::maybe_remove_alias(*unifier.state, actual) {
        Ok(typ) => typ,
        Err(()) => {
            match actual.as_alias_symbol() {
                Some(id) => {
                    unifier.report_error(UnifyError::Other(TypeError::UndefinedType(id.clone())));
                    return Err(());
                }
                None => return Ok(None),
            }
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

fn unify_app<'a, 's, U, E>(unifier: &mut UnifierState<'a, 's, U>,
                           l: &TcType,
                           l_args: &[TcType],
                           r: &TcType)
                           -> Result<Option<TcType>, E>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let mut args = Vec::new();
    unify_app_(unifier, l, l_args, r, false, &mut args);
    if args.is_empty() {
        Ok(None)
    } else {
        Ok(Some(Type::app(l.clone(), args)))
    }
}

fn unify_app_<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                         l: &TcType,
                         l_args: &[TcType],
                         r: &TcType,
                         replaced: bool,
                         output: &mut Vec<TcType>)
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let r = unifier.subs.real(r);
    let new = match **r {
        Type::App(ref r, ref r_args) => {
            use std::cmp::Ordering::*;
            let args_iter = match l_args.len().cmp(&r_args.len()) {
                Equal => {
                    unifier.try_match(l, r);
                    l_args.iter().zip(r_args)
                }
                Less => {
                    let offset = r_args.len() - l_args.len();
                    unifier.try_match(l, &Type::app(r.clone(), r_args[..offset].into()));
                    l_args.iter().zip(&r_args[offset..])
                }
                Greater => {
                    let offset = l_args.len() - r_args.len();
                    unifier.try_match(&Type::app(l.clone(), l_args[..offset].into()), r);
                    r_args.iter().zip(&l_args[offset..])
                }
            };
            // Unify the last min(l_args.len(), r_args.len()) arguments
            match walk_move_types(args_iter, |l, r| unifier.try_match(l, r)) {
                Some(args) => {
                    output.extend(args);
                    return;
                }
                None => None,
            }
        }
        _ => {
            let l = Type::app(l.clone(), l_args.iter().cloned().collect());
            unifier.try_match(&l, r);
            // Dont push the actual type that is applied
            return;
        }
    };
    match new {
        Some(typ) => {
            output.push(typ);
        }
        None if replaced || !output.is_empty() => {
            output.push(r.clone());
        }
        None => (),
    }
}

fn zip_function<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                           arg: &TcType,
                           ret: &TcType,
                           other: &TcType,
                           matcher: &mut FnMut(&mut UnifierState<'a, 's, U>, &TcType, &TcType)
                                               -> Option<TcType>)
                           -> Result<Option<TcType>, Error<Symbol>>
    where U: Unifier<&'a (TypeEnv + 'a), TcType>
{
    let error = || {
        let func = Type::function(vec![arg.clone()], ret.clone());
        debug!("Unify error: {} <=> {}", func, other);
        Err(UnifyError::TypeMismatch(func, other.clone()))
    };
    let subs = unifier.subs;
    let other = subs.real(other);
    let (other_arg, fn_prim, other_ret) = match **other {
        Type::App(ref fn_prim, ref args) if args.len() == 2 => (Some(&args[0]), fn_prim, &args[1]),
        Type::App(ref fn_prim, ref args) if args.len() == 1 => (None, fn_prim, &args[0]),
        _ => return error(),
    };
    match other_arg {
        Some(other_arg) => {
            matcher(unifier,
                    fn_prim,
                    &Type::builtin(types::BuiltinType::Function));
            let new_arg = matcher(unifier, arg, other_arg);
            let new_ret = matcher(unifier, ret, other_ret);
            Ok(merge(arg,
                     new_arg,
                     ret,
                     new_ret,
                     |args, ret| Type::function(vec![args], ret)))
        }
        None => {
            let new_fn = matcher(unifier,
                                 fn_prim,
                                 &Type::app(Type::builtin(types::BuiltinType::Function),
                                             vec![arg.clone()]));
            let new_ret = matcher(unifier, ret, other_ret);
            Ok(merge(fn_prim, new_fn, ret, new_ret, |l, r| Type::app(l, vec![r])))
        }
    }
}

fn walk_move_types<'a, I, F, T>(types: I, mut f: F) -> Option<Vec<T>>
    where I: Iterator<Item = (&'a T, &'a T)>,
          F: FnMut(&'a T, &'a T) -> Option<T>,
          T: Clone + 'a
{
    let mut out = Vec::new();
    walk_move_types2(types, false, &mut out, &mut f);
    if out.is_empty() {
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
    if let Some((l, r)) = types.next() {
        let new = f(l, r);
        walk_move_types2(types, replaced || new.is_some(), output, f);
        match new {
            Some(typ) => {
                output.push(typ);
            }
            None if replaced || !output.is_empty() => {
                output.push(l.clone());
            }
            None => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use base::error::Errors;

    use super::TypeError::FieldMismatch;
    use unify::Error::*;
    use unify::unify;
    use substitution::Substitution;
    use base::types;
    use base::types::{TcType, Type, TypeEnv};
    use tests::*;


    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::init();
        let (x, y, z, w) = (intern("x"), intern("y"), intern("z"), intern("w"));
        let l: TcType = Type::record(vec![],
                                     vec![types::Field {
                                              name: x.clone(),
                                              typ: Type::int(),
                                          },
                                          types::Field {
                                              name: y.clone(),
                                              typ: Type::string(),
                                          }]);
        let r = Type::record(vec![],
                             vec![types::Field {
                                      name: z.clone(),
                                      typ: Type::int(),
                                  },
                                  types::Field {
                                      name: w.clone(),
                                      typ: Type::string(),
                                  }]);
        let subs = Substitution::new();
        let result = unify(&subs, &mut (&() as &TypeEnv), &l, &r);
        assert_eq!(result,
                   Err(Errors {
                       errors: vec![Other(FieldMismatch(x, z)), Other(FieldMismatch(y, w))],
                   }));
    }
}
