use std::fmt;

use pretty::{Arena, DocAllocator};

use base::error::Errors;
use base::symbol::Symbol;
use base::types::ToDoc;

use substitution::{self, Substitutable, Substitution};

#[derive(Debug, PartialEq)]
pub enum Error<T, E> {
    TypeMismatch(T, T),
    Substitution(::substitution::Error<T>),
    Other(E),
}

impl<T, E> fmt::Display for Error<T, E>
where
    T: fmt::Display + for<'a> ToDoc<'a, Arena<'a>, ()>,
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use unify::Error::*;

        match *self {
            TypeMismatch(ref l, ref r) => {
                let arena = Arena::new();
                let doc = chain![&arena;
                    arena.newline(),
                    "Expected:",
                    arena.space(),
                    l.to_doc(&arena, ()).group(),
                    arena.newline(),
                    "Found:",
                    arena.space(),
                    r.to_doc(&arena, ()).group()
                ].group()
                    .nest(4);
                write!(f, "Types do not match:{}", doc.1.pretty(80))
            }
            Substitution(ref err) => err.fmt(f),
            Other(ref err) => write!(f, "{}", err),
        }
    }
}

impl<T, E> From<substitution::Error<T>> for Error<T, E> {
    fn from(err: substitution::Error<T>) -> Self {
        Error::Substitution(err)
    }
}

pub struct UnifierState<S, U: ?Sized> {
    pub state: S,
    pub unifier: U,
}

/// A `Unifier` is a type which implements a unifying strategy between two values.
pub trait Unifier<S, Type>
where
    Type: Unifiable<S>,
{
    /// Reports an error to the `unifier` for cases when returning the error is not possible.
    fn report_error(&mut self, error: Error<Type, Type::Error>);
    /// Attempt to unify `l` and `r` using the strategy of `Self`.
    fn try_match(&mut self, l: &Type, r: &Type) -> Option<Type> {
        match self.try_match_res(l, r) {
            Ok(typ) => typ,
            Err(err) => {
                Self::report_error(self, err);
                Self::error_type(self)
            }
        }
    }
    fn try_match_res(
        &mut self,
        l: &Type,
        r: &Type,
    ) -> Result<Option<Type>, Error<Type, Type::Error>>;

    fn error_type(&mut self) -> Option<Type>;

    /// `true` if the returned type can be replaced by the caller
    fn allow_returned_type_replacement(&self) -> bool {
        true
    }
}

/// A type which can be unified by checking for equivalence between the top level of
/// two instances of the type and then recursively calling into the `unifier` on all sub-terms
pub trait Unifiable<S>: Substitutable + Sized {
    type Error;

    /// Perform one level of equality testing between `self` and `other` and recursively call
    /// back into the `unifier` for unification on any sub-terms.
    ///
    /// Returns `Ok` if the the immediate level of `self` and `other` were equal and optionally
    /// returns a more specific type (if None is returned `self` should be chosen as the type if
    /// that becomes necessary).
    /// Returns `Err` if the immediate level were not equal.
    fn zip_match<U>(
        &self,
        other: &Self,
        unifier: &mut UnifierState<S, U>,
    ) -> Result<Option<Self>, Error<Self, Self::Error>>
    where
        UnifierState<S, U>: Unifier<S, Self>;
}

/// Unify `l` and `r` taking into account and updating the substitution `subs` using the
/// [Union-Find](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) algorithm to
/// resolve which types must be equal.
/// If the unification is successful the returned type is the unified type with as much sharing as
/// possible which lets further computions be more efficient.
pub fn unify<S, T>(
    subs: &Substitution<T>,
    state: S,
    l: &T,
    r: &T,
) -> Result<T, Errors<Error<T, T::Error>>>
where
    T: Unifiable<S> + PartialEq + fmt::Display + fmt::Debug + Clone,
    T::Variable: Clone,
    T::Factory: Clone,
{
    let mut state = UnifierState {
        state: state,
        unifier: Unify {
            errors: Errors::new(),
            subs: subs,
        },
    };

    let typ = state.try_match(l, r);
    if state.unifier.errors.has_errors() {
        Err(state.unifier.errors)
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

struct Unify<'e, T, E>
where
    T: Substitutable + 'e,
{
    errors: Errors<Error<T, E>>,
    subs: &'e Substitution<T>,
}

impl<'e, S, T> Unifier<S, T> for UnifierState<S, Unify<'e, T, T::Error>>
where
    T: Unifiable<S> + PartialEq + Clone + fmt::Display + 'e,
    T::Variable: Clone,
    T::Factory: Clone,
{
    fn report_error(&mut self, error: Error<T, T::Error>) {
        self.unifier.errors.push(error);
    }

    fn try_match_res(&mut self, l_orig: &T, r_orig: &T) -> Result<Option<T>, Error<T, T::Error>> {
        let subs = self.unifier.subs;

        // Retrieve the 'real' types by resolving
        let l = subs.real(l_orig);
        let r = subs.real(r_orig);

        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (l.get_var(), r.get_var()) {
            (_, Some(r_var)) => {
                let replacement = subs.union(r_var, l)?;
                debug!("Union {} <> {}", l, replacement.as_ref().unwrap_or(r));
                Ok(replacement)
            }
            (Some(l_var), _) => {
                let replacement = subs.union(l_var, r)?;
                debug!("Union {} <> {}", replacement.as_ref().unwrap_or(l), r);
                Ok(replacement.or_else(|| Some(r.clone())))
            }
            (None, None) => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                l.zip_match(r, self)
            }
        }
    }

    fn error_type(&mut self) -> Option<T> {
        Some(self.unifier.subs.new_var())
    }
}

pub trait GenericVariant {
    fn new_generic(symbol: Symbol, kind: &Self) -> Self;
}

#[cfg(test)]
mod test {
    use super::*;

    use std::fmt;

    use base::error::Errors;
    use base::merge::merge;
    use base::symbol::Symbol;
    use base::types::Walker;

    use substitution::{Substitutable, Substitution};

    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub struct TType(Box<Type<TType>>);

    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub enum Type<T> {
        Variable(u32),
        Ident(String),
        Arrow(T, T),
    }

    impl fmt::Display for TType {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    impl GenericVariant for TType {
        fn new_generic(symbol: Symbol, _: &TType) -> Self {
            TType(Box::new(Type::Ident(symbol.to_string())))
        }
    }

    impl Substitutable for TType {
        type Variable = u32;
        type Factory = ();

        fn from_variable(var: u32) -> TType {
            TType(Box::new(Type::Variable(var)))
        }
        fn get_var(&self) -> Option<&u32> {
            match *self.0 {
                Type::Variable(ref var) => Some(var),
                _ => None,
            }
        }
        fn traverse<'a, F>(&'a self, f: &mut F)
        where
            F: Walker<'a, Self>,
        {
            fn traverse_<'t>(typ: &'t TType, f: &mut Walker<'t, TType>) {
                match *typ.0 {
                    Type::Arrow(ref a, ref r) => {
                        f.walk(a);
                        f.walk(r);
                    }
                    Type::Variable(_) | Type::Ident(_) => (),
                }
            }
            traverse_(self, f)
        }

        fn instantiate(&self, _subs: &Substitution<Self>) -> Self {
            self.clone()
        }
    }

    impl Unifiable<()> for TType {
        type Error = ();
        fn zip_match<F>(
            &self,
            other: &Self,
            f: &mut UnifierState<(), F>,
        ) -> Result<Option<Self>, Error<Self, Self::Error>>
        where
            UnifierState<(), F>: Unifier<(), Self>,
        {
            match (&*self.0, &*other.0) {
                (&Type::Ident(ref l), &Type::Ident(ref r)) if l == r => Ok(None),
                (&Type::Arrow(ref l1, ref l2), &Type::Arrow(ref r1, ref r2)) => {
                    let arg = f.try_match(l1, r1);
                    let ret = f.try_match(l2, r2);
                    Ok(merge(l1, arg, l2, ret, |a, r| {
                        TType(Box::new(Type::Arrow(a, r)))
                    }))
                }
                _ => Err(Error::TypeMismatch(self.clone(), other.clone())),
            }
        }
    }

    fn unify(
        subs: &Substitution<TType>,
        l: &TType,
        r: &TType,
    ) -> Result<TType, Errors<Error<TType, ()>>> {
        super::unify(subs, (), l, r)
    }

    #[test]
    fn unify_test() {
        let subs = Substitution::new(());
        let var1 = subs.new_var();
        let var2 = subs.new_var();

        let result = unify(&subs, &var1, &var2);
        assert!(result.is_ok());

        let string = TType(Box::new(Type::Ident("String".into())));
        let result = unify(&subs, &var1, &string);
        assert!(result.is_ok());

        let int = TType(Box::new(Type::Ident("Int".into())));
        let result = unify(&subs, &int, &string);
        assert!(result.is_err());
    }

    #[test]
    fn unify_function() {
        let subs = Substitution::<TType>::new(());
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Ident("String".into())));
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
        let subs = Substitution::<TType>::new(());
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Ident("String".into())));
        let result = unify(&subs, &var1, &string);
        assert_eq!(result, Ok(string.clone()));

        let int = TType(Box::new(Type::Ident("Int".into())));
        // Check that var1 does not unify with int as it should already be a string
        let result = unify(&subs, &var1, &int);
        assert_eq!(
            result,
            Err(Errors::from(vec![
                Error::TypeMismatch(string.clone(), int.clone()),
            ],),)
        );
    }

    #[test]
    fn occurs() {
        let subs = Substitution::<TType>::new(());
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Ident("String".into())));
        let fun = TType(Box::new(Type::Arrow(string.clone(), var1.clone())));
        let result = unify(&subs, &fun, &var1);
        assert_eq!(
            result,
            Err(Errors::from(vec![
                Error::Substitution(::substitution::Error::Occurs(var1, fun.clone())),
            ]))
        );
    }
}
