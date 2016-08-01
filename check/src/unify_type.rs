use std::fmt;

use base::ast::ASTType;
use base::types::{self, TcType, Type, TypeVariable, TypeEnv, merge};
use base::symbol::{Symbol, SymbolRef};
use base::instantiate;

use unify;
use unify::{Error as UnifyError, Unifier, Unifiable};
use substitution::{Variable, Substitutable};

pub type Error<I> = UnifyError<ASTType<I>, TypeError<I>>;

pub struct State<'a> {
    env: &'a (TypeEnv + 'a),
    /// A stack of which aliases are currently expanded. Used to determine when an alias is
    /// recursively expanded in which case the unification fails.
    reduced_aliases: Vec<Symbol>,
}

impl<'a> State<'a> {
    pub fn new(env: &'a (TypeEnv + 'a)) -> State<'a> {
        State {
            env: env,
            reduced_aliases: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    UndefinedType(I),
    FieldMismatch(I, I),
    SelfRecursive(I),
}

impl From<instantiate::Error> for Error<Symbol> {
    fn from(error: instantiate::Error) -> Error<Symbol> {
        UnifyError::Other(match error {
            instantiate::Error::UndefinedType(id) => TypeError::UndefinedType(id),
            instantiate::Error::SelfRecursive(id) => TypeError::SelfRecursive(id),
        })
    }
}

impl<I> fmt::Display for TypeError<I>
    where I: fmt::Display + AsRef<str>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeError::FieldMismatch(ref l, ref r) => {
                write!(f,
                       "Field names in record do not match.\n\tExpected: {}\n\tFound: {}",
                       l,
                       r)
            }
            TypeError::UndefinedType(ref id) => write!(f, "Type `{}` does not exist.", id),
            TypeError::SelfRecursive(ref id) => {
                write!(f,
                       "The use of self recursion in type `{}` could not be unified.",
                       id)
            }
        }
    }
}

pub type UnifierState<'a, 's, U> = unify::UnifierState<'s, State<'a>, TcType, U>;

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

    fn traverse<F>(&self, f: &mut F)
        where F: types::Walker<ASTType<I>>
    {
        types::walk_type_(self, f)
    }
}

impl<'a> Unifiable<State<'a>> for TcType {
    type Error = TypeError<Symbol>;

    fn zip_match<'s, U>(&self,
                        other: &Self,
                        mut unifier: UnifierState<'a, 's, U>)
                        -> Result<Option<Self>, Error<Symbol>>
        where U: Unifier<State<'a>, Self>
    {
        let reduced_aliases = unifier.state.reduced_aliases.len();
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
        let result = do_zip_match(l, r, &mut unifier).map(|mut unified_type| {
            // If the match was done through an alias the unified type is likely less precise than
            // `self` or `other`.
            // So just return `None` which means `self` is used as the type if necessary
            if through_alias {
                unified_type.take();
            }
            unified_type
        });
        unifier.state.reduced_aliases.truncate(reduced_aliases);
        result
    }
}

fn do_zip_match<'a, 's, U>(self_: &TcType,
                           other: &TcType,
                           unifier: &mut UnifierState<'a, 's, U>)
                           -> Result<Option<TcType>, Error<Symbol>>
    where U: Unifier<State<'a>, TcType>
{
    debug!("Unifying:\n{:?} <=> {:?}", self_, other);
    match (&**self_, &**other) {
        (&Type::App(ref l, ref l_args), &Type::App(ref r, ref r_args)) => {
            use std::cmp::Ordering::*;
            match l_args.len().cmp(&r_args.len()) {
                Equal => {
                    let new_type = unifier.try_match(l, r);
                    let new_args = walk_move_types(l_args.iter().zip(r_args),
                                                   |l, r| unifier.try_match(l, r));
                    Ok(merge(l, new_type, l_args, new_args, Type::app))
                }
                Less => {
                    let offset = r_args.len() - l_args.len();
                    let new_type =
                        unifier.try_match(l, &Type::app(r.clone(), r_args[..offset].into()));
                    let new_args = walk_move_types(l_args.iter().zip(&r_args[offset..]),
                                                   |l, r| unifier.try_match(l, r));
                    Ok(merge(l, new_type, l_args, new_args, Type::app))
                }
                Greater => {
                    let offset = l_args.len() - r_args.len();
                    let new_type =
                        unifier.try_match(&Type::app(l.clone(), l_args[..offset].into()), r);
                    let new_args = walk_move_types(l_args[offset..].iter().zip(r_args),
                                                   |l, r| unifier.try_match(l, r));
                    Ok(merge(r, new_type, r_args, new_args, Type::app))
                }
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
            } else {
                Ok(try!(try_with_alias(unifier, self_, other)))
            }
        }
    }
}

/// Attempt to unify two alias types.
/// To find a possible successful unification we walk through the alias expansions of `l` to find
/// an expansion which has `r_id` in the spine of the expanded type
fn find_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                         l: TcType,
                         r_id: &SymbolRef)
                         -> Result<Option<TcType>, ()>
    where U: Unifier<State<'a>, TcType>
{
    let reduced_aliases = unifier.state.reduced_aliases.len();
    let result = find_alias_(unifier, l, r_id);
    match result {
        Ok(Some(_)) => (),
        _ => {
            // Remove any alias reductions that were added if no new type is returned
            unifier.state.reduced_aliases.truncate(reduced_aliases);
        }
    }
    result
}

fn find_alias_<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                          mut l: TcType,
                          r_id: &SymbolRef)
                          -> Result<Option<TcType>, ()>
    where U: Unifier<State<'a>, TcType>
{
    let mut did_alias = false;
    loop {
        l = match l.name() {
            Some(l_id) => {
                if let Some((l_id, _)) = l.as_alias() {
                    if unifier.state.reduced_aliases.iter().any(|id| id == l_id) {
                        return Err(());
                    }
                }
                debug!("Looking for alias reduction from `{}` to `{}`", l_id, r_id);
                if l_id == r_id {
                    // If the aliases matched before going through an alias there is no need to
                    // return a replacement type
                    return Ok(if did_alias {
                        Some(l.clone())
                    } else {
                        None
                    });
                }
                did_alias = true;
                match instantiate::maybe_remove_alias(unifier.state.env, &l) {
                    Ok(Some(typ)) => {
                        unifier.state
                            .reduced_aliases
                            .push(l.as_alias().expect("Alias").0.clone());
                        typ
                    }
                    Ok(None) => break,
                    Err(err) => {
                        unifier.report_error(err.into());
                        return Err(());
                    }
                }
            }
            None => break,
        }
    }
    Ok(None)
}

/// Attempt to find a common alias between two types. If the function is successful it returns
/// either the same types that were passed in or two types which have the same alias in their spine
///
/// Example:
/// ```
/// type Test a = | Test a Int
/// type Test2 = Test String
///
/// // try_zip_alias(Test2, Test 0) => Ok((Test String, Test 0))
/// // try_zip_alias(Float, Test 0) => Ok((Float, Test 0))
/// ```
fn try_zip_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                            expected: &TcType,
                            actual: &TcType,
                            through_alias: &mut bool)
                            -> Result<(TcType, TcType), ()>
    where U: Unifier<State<'a>, TcType>
{
    let mut l = expected.clone();
    if let Some(r_id) = actual.name() {
        l = match try!(find_alias(unifier, l.clone(), r_id)) {
            None => l,
            Some(typ) => {
                *through_alias = true;
                return Ok((typ, actual.clone()));
            }
        };
    }
    let mut r = actual.clone();
    if let Some(l_id) = expected.name() {
        r = match try!(find_alias(unifier, r.clone(), l_id)) {
            None => r,
            Some(typ) => {
                *through_alias = true;
                typ
            }
        };
    }
    Ok((l, r))
}

/// As a last ditch effort attempt to unify the types again by expanding the aliases (if the types
/// are alias types).
fn try_with_alias<'a, 's, U>(unifier: &mut UnifierState<'a, 's, U>,
                             expected: &TcType,
                             actual: &TcType)
                             -> Result<Option<TcType>, Error<Symbol>>
    where U: Unifier<State<'a>, TcType>
{
    let l = try!(instantiate::remove_aliases_checked(&mut unifier.state.reduced_aliases,
                                                     unifier.state.env,
                                                     expected));
    let r = try!(instantiate::remove_aliases_checked(&mut unifier.state.reduced_aliases,
                                                     unifier.state.env,
                                                     actual));
    match (&l, &r) {
        (&None, &None) => {
            debug!("Unify error: {} <=> {}", expected, actual);
            Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()))
        }
        _ => {
            let l = l.as_ref().unwrap_or(expected);
            let r = r.as_ref().unwrap_or(actual);
            unifier.try_match(l, r);
            Ok(None)
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
    use super::*;
    use base::error::Errors;

    use super::TypeError::FieldMismatch;
    use unify::Error::*;
    use unify::unify;
    use substitution::Substitution;
    use base::types::{self, TcType, Type};
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
        let env = MockEnv;
        let mut state = State::new(&env);
        let result = unify(&subs, &mut state, &l, &r);
        assert_eq!(result,
                   Err(Errors {
                       errors: vec![Other(FieldMismatch(x, z)), Other(FieldMismatch(y, w))],
                   }));
    }
}
