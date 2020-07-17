use std::fmt;

use pretty::{Arena, DocAllocator};

use crate::base::error::Errors;
use crate::base::kind::ArcKind;
use crate::base::types::ToDoc;

use crate::substitution::{self, Substitutable, Substitution};

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum Error<E, T> {
    TypeMismatch(T, T),
    Substitution(crate::substitution::Error<T>),
    Other(E),
}

impl<I, T> Error<crate::unify_type::TypeError<I, T>, T> {
    pub fn map_t<U>(
        self,
        f: &mut impl FnMut(T) -> U,
    ) -> Error<crate::unify_type::TypeError<I, U>, U>
    where
        T: Clone,
    {
        use crate::unify::Error::*;

        match self {
            TypeMismatch(l, r) => TypeMismatch(f(l), f(r)),
            Substitution(err) => Substitution(err.map_t(f)),
            Other(err) => Other(err.map_t(f)),
        }
    }
}

impl<I, T> Error<crate::kindcheck::KindError<I, T>, ArcKind> {
    pub fn map_t<U>(
        self,
        f: &mut impl FnMut(T) -> U,
    ) -> Error<crate::kindcheck::KindError<I, U>, ArcKind>
    where
        T: Clone,
    {
        use crate::unify::Error::*;

        match self {
            TypeMismatch(l, r) => TypeMismatch(l, r),
            Substitution(err) => Substitution(err),
            Other(err) => Other(err.map_t(f)),
        }
    }
}

impl<E, T> fmt::Display for Error<E, T>
where
    T: fmt::Display + for<'a> ToDoc<'a, Arena<'a, ()>, (), ()>,
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use crate::unify::Error::*;

        match *self {
            TypeMismatch(ref l, ref r) => {
                let arena = Arena::new();
                let doc = chain![
                    &arena,
                    arena.hardline(),
                    "Expected:",
                    arena.space(),
                    l.to_doc(&arena, ()).group(),
                    arena.hardline(),
                    "Found:",
                    arena.space(),
                    r.to_doc(&arena, ()).group()
                ]
                .group()
                .nest(4);
                write!(f, "Types do not match:{}", doc.1.pretty(80))
            }
            Substitution(ref err) => err.fmt(f),
            Other(ref err) => write!(f, "{}", err),
        }
    }
}

impl<T, E> From<substitution::Error<T>> for Error<E, T> {
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
    fn report_error(&mut self, error: Error<Type::Error, Type>);
    /// Attempt to unify `l` and `r` using the strategy of `Self`.
    fn try_match(&mut self, l: &Type, r: &Type) -> Option<Type> {
        match self.try_match_res(l, r) {
            Ok(typ) => typ,
            Err(err) => {
                Self::report_error(self, err);
                Some(Self::error_type(self))
            }
        }
    }
    fn try_match_res(
        &mut self,
        l: &Type,
        r: &Type,
    ) -> Result<Option<Type>, Error<Type::Error, Type>>;

    /// `true` if the returned type can be replaced by the caller
    fn allow_returned_type_replacement(&self) -> bool {
        true
    }

    fn error_type(&self) -> Type;
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
    ) -> Result<Option<Self>, Error<Self::Error, Self>>
    where
        UnifierState<S, U>: Unifier<S, Self>;

    fn error_type(state: &S) -> Self;
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
) -> Result<T, Errors<Error<T::Error, T>>>
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
    errors: Errors<Error<E, T>>,
    subs: &'e Substitution<T>,
}

impl<'e, S, T> Unifier<S, T> for UnifierState<S, Unify<'e, T, T::Error>>
where
    T: Unifiable<S> + PartialEq + Clone + fmt::Display + 'e,
    T::Variable: Clone,
    T::Factory: Clone,
{
    fn report_error(&mut self, error: Error<T::Error, T>) {
        self.unifier.errors.push(error);
    }

    fn try_match_res(&mut self, l_orig: &T, r_orig: &T) -> Result<Option<T>, Error<T::Error, T>> {
        let subs = self.unifier.subs;

        // Retrieve the 'real' types by resolving
        let l = subs.real(l_orig);
        let r = subs.real(r_orig);

        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (l.get_var(), r.get_var()) {
            (_, Some(_)) => {
                debug!("Union {} <> {}", l, r);
                subs.union(r, l)?;
                Ok(None)
            }
            (Some(_), _) => {
                debug!("Union {} <> {}", l, r);
                subs.union(l, r)?;
                Ok(Some(r.clone()))
            }
            (None, None) => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                l.zip_match(r, self)
            }
        }
    }

    fn error_type(&self) -> T {
        T::error_type(&self.state)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::{fmt, ops::Deref};

    use crate::base::{
        error::Errors,
        merge::merge,
        types::{NullInterner, Walker},
    };

    use crate::substitution::{Substitutable, Substitution};

    #[derive(Debug, Default, Clone, Eq, PartialEq, Hash)]
    pub struct TType(Box<Type<TType>>);

    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub enum Type<T> {
        Variable(u32),
        Ident(String),
        Arrow(T, T),
    }

    impl<T> Default for Type<T> {
        fn default() -> Self {
            Type::Variable(0)
        }
    }

    impl Deref for TType {
        type Target = Type<TType>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl fmt::Display for TType {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    impl Substitutable for TType {
        type Variable = u32;
        type Factory = ();
        type Interner = NullInterner;

        fn from_variable(_: &Substitution<Self>, var: u32) -> TType {
            TType(Box::new(Type::Variable(var)))
        }

        fn into_variable(&mut self, x: Self::Variable) {
            *self.0 = Type::Variable(x);
        }

        fn is_unique(_: &Self) -> bool {
            true
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
            fn traverse_<'t>(typ: &'t TType, f: &mut dyn Walker<'t, TType>) {
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
        ) -> Result<Option<Self>, Error<Self::Error, Self>>
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
        fn error_type(_: &()) -> Self {
            TType(Box::new(Type::Variable(0)))
        }
    }

    fn unify(
        subs: &Substitution<TType>,
        l: &TType,
        r: &TType,
    ) -> Result<TType, Errors<Error<(), TType>>> {
        super::unify(subs, (), l, r)
    }

    #[test]
    fn unify_test() {
        let subs = Substitution::default();
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
        let subs = Substitution::<TType>::default();
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
        let subs = Substitution::<TType>::default();
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Ident("String".into())));
        let result = unify(&subs, &var1, &string);
        assert_eq!(result.as_ref().map(|t| subs.real(t)), Ok(&string));

        let int = TType(Box::new(Type::Ident("Int".into())));
        // Check that var1 does not unify with int as it should already be a string
        let result = unify(&subs, &var1, &int);
        assert_eq!(
            result,
            Err(Errors::from(vec![Error::TypeMismatch(
                string.clone(),
                int.clone(),
            )],),)
        );
    }

    #[test]
    fn occurs() {
        let subs = Substitution::<TType>::default();
        let var1 = subs.new_var();

        let string = TType(Box::new(Type::Ident("String".into())));
        let fun = TType(Box::new(Type::Arrow(string.clone(), var1.clone())));
        let result = unify(&subs, &fun, &var1);
        assert_eq!(
            result,
            Err(Errors::from(vec![Error::Substitution(
                crate::substitution::Error::Occurs(var1, fun.clone()),
            )]))
        );
    }
}
