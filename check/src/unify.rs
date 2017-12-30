use std::fmt;
use std::hash::Hash;

use pretty::{Arena, DocAllocator};

use base::error::Errors;
use base::fnv::FnvMap;
use base::symbol::{Symbol, Symbols};
use base::types::ToDoc;

use substitution::{self, Substitutable, Substitution, Variable};

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

pub struct UnifierState<S, U> {
    pub state: S,
    pub unifier: U,
}

impl<S, U> UnifierState<S, U> {
    pub fn report_error<Type>(&mut self, error: Error<Type, Type::Error>)
    where
        U: Unifier<S, Type>,
        Type: Unifiable<S>,
    {
        Unifier::report_error(self, error)
    }

    pub fn try_match_res<Type>(
        &mut self,
        l: &Type,
        r: &Type,
    ) -> Result<Option<Type>, Error<Type, Type::Error>>
    where
        U: Unifier<S, Type>,
        Type: Unifiable<S>,
    {
        Unifier::try_match_res(self, l, r)
    }

    pub fn try_match<Type>(&mut self, l: &Type, r: &Type) -> Option<Type>
    where
        U: Unifier<S, Type>,
        Type: Unifiable<S>,
    {
        Unifier::try_match(self, l, r)
    }
}

/// A `Unifier` is a type which implements a unifying strategy between two values.
pub trait Unifier<S, Type>: Sized
where
    Type: Unifiable<S>,
{
    /// Reports an error to the `unifier` for cases when returning the error is not possible.
    fn report_error(unifier: &mut UnifierState<S, Self>, error: Error<Type, Type::Error>);
    /// Attempt to unify `l` and `r` using the strategy of `Self`.
    fn try_match(unifier: &mut UnifierState<S, Self>, l: &Type, r: &Type) -> Option<Type> {
        match unifier.try_match_res(l, r) {
            Ok(typ) => typ,
            Err(err) => {
                Self::report_error(unifier, err);
                Self::error_type(unifier)
            }
        }
    }
    fn try_match_res(
        unifier: &mut UnifierState<S, Self>,
        l: &Type,
        r: &Type,
    ) -> Result<Option<Type>, Error<Type, Type::Error>>;

    fn error_type(unifier: &mut UnifierState<S, Self>) -> Option<Type>;

    /// `true` if the returned type can be replaced by the caller
    fn allow_returned_type_replacement() -> bool {
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
        U: Unifier<S, Self>;
}

pub trait Fresh {
    fn fresh(&self) -> Self;
}

impl Fresh for () {
    fn fresh(&self) -> Self {
        *self
    }
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
    S: Fresh,
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

impl<'e, S, T> Unifier<S, T> for Unify<'e, T, T::Error>
where
    T: Unifiable<S> + PartialEq + Clone + fmt::Display + 'e,
    T::Variable: Clone,
    T::Factory: Clone,
    S: Fresh,
{
    fn report_error(unifier: &mut UnifierState<S, Self>, error: Error<T, T::Error>) {
        unifier.unifier.errors.push(error);
    }

    fn try_match_res(
        unifier: &mut UnifierState<S, Self>,
        l_orig: &T,
        r_orig: &T,
    ) -> Result<Option<T>, Error<T, T::Error>> {
        let subs = unifier.unifier.subs;

        // Retrieve the 'real' types by resolving
        let l = subs.real(l_orig);
        let r = subs.real(r_orig);

        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (l.get_var(), r.get_var()) {
            (_, Some(r_var)) => {
                let replacement = subs.union(|| unifier.state.fresh(), r_var, l)?;
                debug!("Union {} <> {}", l, replacement.as_ref().unwrap_or(r));
                Ok(replacement)
            }
            (Some(l_var), _) => {
                let replacement = subs.union(|| unifier.state.fresh(), l_var, r)?;
                debug!("Union {} <> {}", replacement.as_ref().unwrap_or(l), r);
                Ok(replacement.or_else(|| Some(r.clone())))
            }
            (None, None) => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                l.zip_match(r, unifier)
            }
        }
    }

    fn error_type(unifier: &mut UnifierState<S, Self>) -> Option<T> {
        Some(unifier.unifier.subs.new_var())
    }
}

pub trait GenericVariant {
    fn new_generic(symbol: Symbol, kind: &Self) -> Self;
}

/// Calculates the intersection between two types. The intersection between two types is the most
/// specialized type which both types can sucessfully unify to.
///
/// # Example
/// intersect (Int -> Int -> Bool) <=> (Float -> Float -> Bool) ==> (a -> a -> Bool)
pub fn intersection<S, T>(
    subs: &Substitution<T>,
    symbols: &mut Symbols,
    state: S,
    l: &T,
    r: &T,
) -> (FnvMap<(T, T), Symbol>, T)
where
    T: GenericVariant + Unifiable<S> + Eq + Clone + Hash,
    T::Variable: Clone,
{
    let mut unifier = UnifierState {
        state: state,
        unifier: Intersect {
            constraints: FnvMap::default(),
            symbols: symbols,
            subs: subs,
        },
    };
    let typ = unifier.try_match(l, r).unwrap_or_else(|| l.clone());
    (unifier.unifier.constraints, typ)
}

struct Intersect<'m, T: 'm>
where
    T: Substitutable,
{
    constraints: FnvMap<(T, T), Symbol>,
    symbols: &'m mut Symbols,
    subs: &'m Substitution<T>,
}

impl<'m, S, T> Unifier<S, T> for Intersect<'m, T>
where
    T: GenericVariant + Unifiable<S> + Eq + Clone + Hash,
    T::Variable: Clone,
{
    fn report_error(_unifier: &mut UnifierState<S, Self>, _error: Error<T, T::Error>) {}

    fn try_match_res(
        unifier: &mut UnifierState<S, Self>,
        l: &T,
        r: &T,
    ) -> Result<Option<T>, Error<T, T::Error>> {
        let subs = unifier.unifier.subs;
        let l = subs.real(l);
        let r = subs.real(r);
        match (l.get_var(), r.get_var()) {
            (Some(l), Some(r)) if l.get_id() == r.get_id() => Ok(None),
            _ => {
                match l.zip_match(r, unifier) {
                    Ok(typ) => Ok(typ),
                    Err(_) => {
                        // If the immediate level of `l` and `r` does not match, record
                        // the mismatched types return a type variable in their place
                        // (Reusing a variable if the same mismatch was already seen)
                        let symbols = &mut unifier.unifier.symbols;
                        let generic_symbol = unifier
                            .unifier
                            .constraints
                            .entry((l.clone(), r.clone()))
                            .or_insert_with(|| {
                                let len = symbols.len();
                                symbols.symbol(format!("abc{}", len))
                            });
                        Ok(Some(T::new_generic(generic_symbol.clone(), l)))
                    }
                }
            }
        }
    }
    fn error_type(_unifier: &mut UnifierState<S, Self>) -> Option<T> {
        None
    }

    fn allow_returned_type_replacement() -> bool {
        false
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::fmt;

    use base::error::Errors;
    use base::merge::merge;
    use base::symbol::{Symbol, Symbols};
    use base::types::Walker;

    use substitution::{Constraints, Substitutable, Substitution};

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

    impl TType {
        fn ident(s: &str) -> TType {
            TType(Box::new(Type::Ident(s.into())))
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

        fn instantiate(
            &self,
            _subs: &Substitution<Self>,
            _constraints: &FnvMap<Symbol, Constraints<Self>>,
        ) -> Self {
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
            F: Unifier<(), Self>,
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

    fn mk_fn(a: &TType, r: &TType) -> TType {
        TType(Box::new(Type::Arrow(a.clone(), r.clone())))
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

    #[test]
    fn intersection_test() {
        fn intersection(subs: &Substitution<TType>, l: &TType, r: &TType) -> TType {
            let mut symbols = Symbols::new();
            super::intersection(subs, &mut symbols, (), l, r).1
        }

        let subs = Substitution::<TType>::new(());
        let var1 = subs.new_var();
        let string = TType(Box::new(Type::Ident("String".into())));
        let int = TType(Box::new(Type::Ident("Int".into())));

        let string_fun = mk_fn(&string, &string);
        let int_fun = mk_fn(&int, &int);
        let result = intersection(&subs, &int_fun, &string_fun);
        assert_eq!(result, mk_fn(&TType::ident("abc0"), &TType::ident("abc0")));

        let var_fun = mk_fn(&var1, &var1);
        let result = intersection(&subs, &int_fun, &var_fun);
        assert_eq!(result, mk_fn(&TType::ident("abc0"), &TType::ident("abc0")));
    }
}
