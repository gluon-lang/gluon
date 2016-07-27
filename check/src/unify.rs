use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

use base::error::Errors;

use substitution::{Substitution, Substitutable, Variable};

#[derive(Debug, PartialEq)]
pub enum Error<T: Substitutable, E> {
    TypeMismatch(T, T),
    Occurs(T::Variable, T),
    Other(E),
}

impl<T, E> fmt::Display for Error<T, E>
    where T: Substitutable + fmt::Display,
          T::Variable: fmt::Display,
          E: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use unify::Error::*;
        match *self {
            TypeMismatch(ref l, ref r) => {
                write!(f, "Types do not match:\n\tExpected: {}\n\tFound: {}", l, r)
            }
            Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
            Other(ref err) => write!(f, "{}", err),
        }
    }
}


pub struct UnifierState<'s, S: ?Sized + 's, T: 's, U> {
    pub state: &'s mut S,
    pub subs: &'s Substitution<T>,
    pub unifier: U,
}

impl<'s, S: ?Sized, Type, U> UnifierState<'s, S, Type, U>
    where U: Unifier<S, Type>,
          Type: Unifiable<S>
{
    pub fn report_error(&mut self, error: Error<Type, Type::Error>) {
        Unifier::report_error(self, error)
    }

    pub fn try_match(&mut self, l: &Type, r: &Type) -> Option<Type> {
        Unifier::try_match(self, l, r)
    }
}

pub trait Unifier<S: ?Sized, Type>: Sized
    where Type: Unifiable<S>
{
    fn report_error(unifier: &mut UnifierState<S, Type, Self>, error: Error<Type, Type::Error>);
    fn try_match(unifier: &mut UnifierState<S, Type, Self>, l: &Type, r: &Type) -> Option<Type>;
}

pub trait Unifiable<S: ?Sized>: Substitutable + Sized {
    type Error;

    fn zip_match<U>(&self,
                    other: &Self,
                    unifier: UnifierState<S, Self, U>)
                    -> Result<Option<Self>, Error<Self, Self::Error>>
        where U: Unifier<S, Self>;
}

/// Unify `l` and `r` taking into account and updating the substitution `subs`
/// If the unification is successful the returned type is the unified type with as much sharing as
/// possible which lets further computions be more efficient.
pub fn unify<S, T>(subs: &Substitution<T>,
                   state: &mut S,
                   l: &T,
                   r: &T)
                   -> Result<T, Errors<Error<T, T::Error>>>
    where T: Unifiable<S> + PartialEq + Clone,
          T::Variable: Clone
{
    let mut errors = Errors::new();
    let typ = UnifierState {
            state: state,
            subs: subs,
            unifier: Unify { errors: &mut errors },
        }
        .try_match(l, r);
    if errors.has_errors() {
        Err(errors)
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

struct Unify<'e, T, E: 'e>
    where T: Substitutable + 'e
{
    errors: &'e mut Errors<Error<T, E>>,
}

impl<'e, S, T> Unifier<S, T> for Unify<'e, T, T::Error>
    where T: Unifiable<S> + PartialEq + Clone + 'e,
          T::Variable: Clone
{
    fn report_error(unifier: &mut UnifierState<S, T, Self>, error: Error<T, T::Error>) {
        unifier.unifier.errors.error(error);
    }

    fn try_match(unifier: &mut UnifierState<S, T, Self>, l: &T, r: &T) -> Option<T> {
        let subs = unifier.subs;
        let mut errors = &mut unifier.unifier.errors;
        let l = subs.real(l);
        let r = subs.real(r);
        match (l.get_var(), r.get_var()) {
            (Some(l), Some(r)) if l.get_id() == r.get_id() => None,
            (_, Some(r)) => {
                match subs.union(r, l) {
                    Ok(()) => Some(l.clone()),
                    Err(()) => {
                        errors.error(Error::Occurs(r.clone(), l.clone()));
                        Some(subs.new_var())
                    }
                }
            }
            (Some(l), _) => {
                match subs.union(l, r) {
                    Ok(()) => Some(r.clone()),
                    Err(()) => {
                        errors.error(Error::Occurs(l.clone(), r.clone()));
                        Some(subs.new_var())
                    }
                }
            }
            (None, None) => {
                let result = {
                    let next_unifier = UnifierState {
                        state: unifier.state,
                        subs: subs,
                        unifier: Unify { errors: errors },
                    };
                    l.zip_match(r, next_unifier)
                };
                match result {
                    Ok(typ) => typ,
                    Err(error) => {
                        errors.error(error);
                        Some(subs.new_var())
                    }
                }
            }
        }
    }
}

/// Calculates the intersection between two types. The intersection between two types is the most
/// specialized type which both types can sucessfully unify to.
///
/// # Example
/// intersect (Int -> Int -> Bool) <=> (Float -> Float -> Bool) ==> (a -> a -> Bool)
pub fn intersection<S, T>(subs: &Substitution<T>, state: &mut S, l: &T, r: &T) -> T
    where T: Unifiable<S> + Eq + Clone + Hash,
          T::Variable: Clone
{
    let mut map = HashMap::new();
    let mut unifier = UnifierState {
        state: state,
        subs: subs,
        unifier: Intersect { mismatch_map: &mut map },
    };
    unifier.try_match(l, r).unwrap_or_else(|| l.clone())
}

struct Intersect<'m, T: 'm> {
    mismatch_map: &'m mut HashMap<(T, T), T>,
}

impl<'m, S, T> Unifier<S, T> for Intersect<'m, T>
    where T: Unifiable<S> + Eq + Hash + Clone,
          T::Variable: Clone
{
    fn report_error(_unifier: &mut UnifierState<S, T, Self>, _error: Error<T, T::Error>) {}

    fn try_match(unifier: &mut UnifierState<S, T, Self>, l: &T, r: &T) -> Option<T> {
        let subs = unifier.subs;
        let l = subs.real(l);
        let r = subs.real(r);
        match (l.get_var(), r.get_var()) {
            (Some(l), Some(r)) if l.get_id() == r.get_id() => None,
            _ => {
                let result = {
                    let next_unifier = UnifierState {
                        state: unifier.state,
                        subs: subs,
                        unifier: Intersect { mismatch_map: unifier.unifier.mismatch_map },
                    };
                    l.zip_match(r, next_unifier)
                };
                match result {
                    Ok(typ) => typ,
                    Err(_) => {
                        Some(unifier.unifier
                            .mismatch_map
                            .entry((l.clone(), r.clone()))
                            .or_insert_with(|| subs.new_var())
                            .clone())
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use base::types::merge;
    use base::error::Errors;

    use super::{Error, Unifier, Unifiable, UnifierState};
    use substitution::{Substitution, Substitutable};

    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub struct TType(Box<Type<TType>>);

    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub enum Type<T> {
        Variable(u32),
        Id(String),
        Arrow(T, T),
    }


    impl Substitutable for TType {
        type Variable = u32;
        fn new(var: u32) -> TType {
            TType(Box::new(Type::Variable(var)))
        }
        fn get_var(&self) -> Option<&u32> {
            match *self.0 {
                Type::Variable(ref var) => Some(var),
                _ => None,
            }
        }
        fn traverse<'s, F>(&'s self, mut f: F)
            where F: FnMut(&'s Self) -> &'s Self
        {
            fn traverse_<'s>(typ: &'s TType, f: &mut FnMut(&'s TType) -> &'s TType) {
                match *f(typ).0 {
                    Type::Arrow(ref a, ref r) => {
                        traverse_(a, f);
                        traverse_(r, f);
                    }
                    Type::Variable(_) |
                    Type::Id(_) => (),
                }
            }
            traverse_(self, &mut f)
        }
    }

    impl Unifiable<()> for TType {
        type Error = ();
        fn zip_match<F>(&self,
                        other: &Self,
                        mut f: UnifierState<(), Self, F>)
                        -> Result<Option<Self>, Error<Self, Self::Error>>
            where F: Unifier<(), Self>
        {
            match (&*self.0, &*other.0) {
                (&Type::Id(ref l), &Type::Id(ref r)) if l == r => Ok(None),
                (&Type::Arrow(ref l1, ref l2), &Type::Arrow(ref r1, ref r2)) => {
                    let arg = f.try_match(l1, r1);
                    let ret = f.try_match(l2, r2);
                    Ok(merge(l1, arg, l2, ret, |a, r| TType(Box::new(Type::Arrow(a, r)))))
                }
                _ => Err(Error::TypeMismatch(self.clone(), other.clone())),
            }
        }
    }

    fn mk_fn(a: &TType, r: &TType) -> TType {
        TType(Box::new(Type::Arrow(a.clone(), r.clone())))
    }

    fn unify(subs: &Substitution<TType>,
             l: &TType,
             r: &TType)
             -> Result<TType, Errors<Error<TType, ()>>> {
        super::unify(subs, &mut (), l, r)
    }

    #[test]
    fn unify_test() {
        let subs = Substitution::new();
        let var1 = subs.new_var();
        let var2 = subs.new_var();

        let result = unify(&subs, &var1, &var2);
        assert!(result.is_ok());

        let string = TType(Box::new(Type::Id("String".into())));
        let result = unify(&subs, &var1, &string);
        assert!(result.is_ok());

        let int = TType(Box::new(Type::Id("Int".into())));
        let result = unify(&subs, &int, &string);
        assert!(result.is_err());
    }

    #[test]
    fn unify_function() {
        let subs = Substitution::<TType>::new();
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Id("String".into())));
        let fun = TType(Box::new(Type::Arrow(string.clone(), var1.clone())));
        let result = unify(&subs, &fun, &string);
        assert!(result.is_err());

        let fun2 = TType(Box::new(Type::Arrow(string.clone(), string.clone())));
        let result = unify(&subs, &fun, &fun2);
        assert!(result.is_ok());
        assert_eq!(subs.real(&var1), &string);
    }

    #[test]
    fn unify_real_type() {
        let subs = Substitution::<TType>::new();
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Id("String".into())));
        let result = unify(&subs, &var1, &string);
        assert_eq!(result, Ok(string.clone()));

        let int = TType(Box::new(Type::Id("Int".into())));
        // Check that var1 does not unify with int as it should already be a string
        let result = unify(&subs, &var1, &int);
        assert_eq!(result,
                   Err(Errors { errors: vec![Error::TypeMismatch(string.clone(), int.clone())] }));
    }

    #[test]
    fn occurs() {
        let subs = Substitution::<TType>::new();
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Id("String".into())));
        let fun = TType(Box::new(Type::Arrow(string.clone(), var1.clone())));
        let result = unify(&subs, &fun, &var1);
        assert_eq!(result,
                   Err(Errors {
                       errors: vec![Error::Occurs(*var1.get_var().unwrap(), fun.clone())],
                   }));
    }

    fn intersection(subs: &Substitution<TType>, l: &TType, r: &TType) -> TType {
        super::intersection(subs, &mut (), l, r)
    }
    #[test]
    fn intersection_test() {
        let subs = Substitution::<TType>::new();
        let var1 = subs.new_var();
        let string = TType(Box::new(Type::Id("String".into())));
        let int = TType(Box::new(Type::Id("Int".into())));

        let string_fun = mk_fn(&string, &string);
        let int_fun = mk_fn(&int, &int);
        let result = intersection(&subs, &int_fun, &string_fun);
        assert_eq!(result, mk_fn(&TType::new(2), &TType::new(2)));

        let var_fun = mk_fn(&var1, &var1);
        let result = intersection(&subs, &int_fun, &var_fun);
        assert_eq!(result, mk_fn(&TType::new(3), &TType::new(3)));
    }
}
