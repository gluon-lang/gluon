use std::fmt;
use std::mem;

use base::error::Errors;
use base::fnv::FnvMap;
use base::merge;
use base::kind::ArcKind;
use base::types::{self, AppVec, ArcType, Field, Generic, Type, TypeEnv, TypeVariable};
use base::symbol::{Symbol, SymbolRef};
use base::resolve::{self, Error as ResolveError};
use base::scoped_map::ScopedMap;

use unify;
use unify::{Error as UnifyError, Fresh, GenericVariant, Unifiable, Unifier};
use substitution::{Constraints, Substitutable, Substitution, Variable, VariableFactory};

impl VariableFactory for ArcKind {
    type Variable = TypeVariable;
    fn new(&self, id: u32) -> TypeVariable {
        TypeVariable {
            id: id,
            kind: self.clone(),
        }
    }
}

impl GenericVariant for ArcType {
    fn new_generic(symbol: Symbol, kind: &Self) -> Self {
        Type::generic(Generic {
            id: symbol,
            kind: kind.kind().into_owned(),
        })
    }
}

pub type Error<I> = UnifyError<ArcType<I>, TypeError<I>>;

#[derive(Clone)]
pub struct State<'a> {
    env: &'a (TypeEnv + 'a),
    /// A stack of which aliases are currently expanded. Used to determine when an alias is
    /// recursively expanded in which case the unification fails.
    reduced_aliases: Vec<Symbol>,
    subs: &'a Substitution<ArcType>,
    record_context: Option<(ArcType, ArcType)>,
}

impl<'a> Fresh for State<'a> {
    fn fresh(&self) -> Self {
        State::new(self.env, self.subs)
    }
}

impl<'a> State<'a> {
    pub fn new(env: &'a (TypeEnv + 'a), subs: &'a Substitution<ArcType>) -> State<'a> {
        State {
            env: env,
            reduced_aliases: Vec::new(),
            subs: subs,
            record_context: None,
        }
    }

    fn remove_aliases(&mut self, typ: &ArcType) -> Result<Option<ArcType>, TypeError<Symbol>> {
        if let Some(alias_id) = typ.alias_ident() {
            if self.reduced_aliases.iter().any(|name| name == alias_id) {
                return Err(TypeError::SelfRecursive(alias_id.clone()));
            }
            self.reduced_aliases.push(alias_id.clone());
        }

        match resolve::remove_alias(&self.env, typ)? {
            Some(mut typ) => {
                loop {
                    if let Some(alias_id) = typ.alias_ident() {
                        if self.reduced_aliases.iter().any(|name| name == alias_id) {
                            return Err(TypeError::SelfRecursive(alias_id.clone()));
                        }
                        self.reduced_aliases.push(alias_id.clone());
                    }

                    match resolve::remove_alias(&self.env, &typ)? {
                        Some(new_typ) => typ = new_typ,
                        None => break,
                    }
                }
                Ok(Some(typ))
            }
            None => Ok(None),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    UndefinedType(I),
    FieldMismatch(I, I),
    SelfRecursive(I),
    UnableToGeneralize(I),
    MissingFields(ArcType<I>, Vec<I>),
}

impl From<ResolveError> for TypeError<Symbol> {
    fn from(error: ResolveError) -> TypeError<Symbol> {
        match error {
            ResolveError::UndefinedType(id) => TypeError::UndefinedType(id),
        }
    }
}

impl<I> fmt::Display for TypeError<I>
where
    I: fmt::Display + AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeError::FieldMismatch(ref l, ref r) => write!(
                f,
                "Field names in record do not match.\n\tExpected: {}\n\tFound: {}",
                l,
                r
            ),
            TypeError::UndefinedType(ref id) => write!(f, "Type `{}` does not exist.", id),
            TypeError::SelfRecursive(ref id) => write!(
                f,
                "The use of self recursion in type `{}` could not be unified.",
                id
            ),
            TypeError::UnableToGeneralize(ref id) => write!(
                f,
                "Could not generalize the variable bound to `{}` as the variable was used \
                 outside its scope",
                id
            ),
            TypeError::MissingFields(ref typ, ref fields) => {
                write!(f, "The type `{}` lacks the following fields: ", typ)?;
                for (i, field) in fields.iter().enumerate() {
                    let sep = match i {
                        0 => "",
                        i if i < fields.len() - 1 => ", ",
                        _ => " and ",
                    };
                    write!(f, "{}{}", sep, field)?;
                }
                Ok(())
            }
        }
    }
}

pub type UnifierState<'a, U> = unify::UnifierState<State<'a>, U>;

impl Variable for TypeVariable {
    fn get_id(&self) -> u32 {
        self.id
    }
}

impl Substitutable for ArcType<Symbol> {
    type Variable = TypeVariable;
    type Factory = ArcKind;

    fn from_variable(var: TypeVariable) -> Self {
        Type::variable(var)
    }

    fn get_var(&self) -> Option<&TypeVariable> {
        match **self {
            Type::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn traverse<F>(&self, f: &mut F)
    where
        F: types::Walker<Self>,
    {
        types::walk_type_(self, f)
    }

    fn instantiate(
        &self,
        subs: &Substitution<Self>,
        constraints: &FnvMap<Symbol, Constraints<Self>>,
    ) -> Self {
        let mut named_variables = FnvMap::default();
        instantiate_generic_variables(&mut named_variables, subs, constraints, self)
    }
}

impl<'a> Unifiable<State<'a>> for ArcType {
    type Error = TypeError<Symbol>;

    fn zip_match<U>(
        &self,
        other: &Self,
        unifier: &mut UnifierState<'a, U>,
    ) -> Result<Option<Self>, Error<Symbol>>
    where
        U: Unifier<State<'a>, Self>,
    {
        let reduced_aliases = unifier.state.reduced_aliases.len();
        debug!("{} <=> {}", self, other);
        let (l_temp, r_temp);
        let (mut l, mut r) = (self, other);
        let mut through_alias = false;
        match find_common_alias(unifier, self, other, &mut through_alias) {
            Ok((l2, r2)) => {
                l_temp = l2;
                r_temp = r2;
                l = &l_temp;
                r = &r_temp;
            }
            Err(()) => (),
        }
        let result = do_zip_match(unifier, l, r).map(|mut unified_type| {
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

fn do_zip_match<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    expected: &ArcType,
    actual: &ArcType,
) -> Result<Option<ArcType>, Error<Symbol>>
where
    U: Unifier<State<'a>, ArcType>,
{
    debug!("Unifying:\n{} <=> {}", expected, actual);
    match (&**expected, &**actual) {
        (&Type::App(ref l, ref l_args), &Type::App(ref r, ref r_args)) => {
            Ok(unify_app(unifier, l, l_args, r, r_args))
        }
        (&Type::Variant(ref l_row), &Type::Variant(ref r_row)) => match (&**l_row, &**r_row) {
            (
                &Type::ExtendRow {
                    fields: ref l_row,
                    rest: ref l_rest,
                    ..
                },
                &Type::ExtendRow {
                    fields: ref r_row,
                    rest: ref r_rest,
                    ..
                },
            ) => if l_row.len() == r_row.len() &&
                l_row
                    .iter()
                    .zip(r_row)
                    .all(|(l, r)| l.name.name_eq(&r.name)) && l_rest == r_rest
            {
                let iter = l_row.iter().zip(r_row);
                let new_fields = merge::merge_tuple_iter(iter, |l, r| {
                    unifier
                        .try_match(&l.typ, &r.typ)
                        .map(|typ| Field::new(l.name.clone(), typ))
                });
                Ok(
                    new_fields.map(|fields| Type::poly_variant(fields, l_rest.clone())),
                )
            } else {
                Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()))
            },
            _ => Err(UnifyError::TypeMismatch(expected.clone(), actual.clone())),
        },
        (&Type::Record(ref l_row), &Type::Record(ref r_row)) => {
            // Store the current records so that they can be used when displaying field errors
            let previous = mem::replace(
                &mut unifier.state.record_context,
                Some((expected.clone(), actual.clone())),
            );
            let result = unifier
                .try_match(l_row, r_row)
                .map(|row| ArcType::from(Type::Record(row)));
            unifier.state.record_context = previous;
            Ok(result)
        }
        (
            &Type::ExtendRow {
                types: ref l_types,
                fields: ref l_args,
                rest: ref l_rest,
            },
            &Type::ExtendRow {
                types: ref r_types,
                fields: ref r_args,
                rest: ref r_rest,
            },
        ) => {
            // When the field names of both rows match exactly we special case
            // unification to maximize sharing through `merge` and `walk_move_type`
            if l_args.len() == r_args.len() &&
                l_args
                    .iter()
                    .zip(r_args)
                    .all(|(l, r)| l.name.name_eq(&r.name)) && l_types == r_types
            {
                let new_args = merge::merge_tuple_iter(l_args.iter().zip(r_args), |l, r| {
                    unifier
                        .try_match(&l.typ, &r.typ)
                        .map(|typ| Field::new(l.name.clone(), typ))
                });
                let new_rest = unifier.try_match(l_rest, r_rest);
                Ok(merge::merge(
                    l_args,
                    new_args,
                    l_rest,
                    new_rest,
                    |fields, rest| Type::extend_row(l_types.clone(), fields, rest),
                ))
            } else if **l_rest == Type::EmptyRow && **r_rest == Type::EmptyRow {
                for l_typ in expected.type_field_iter() {
                    if actual
                        .type_field_iter()
                        .find(|r_typ| *r_typ == l_typ)
                        .is_none()
                    {
                        return Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()));
                    }
                }

                // HACK For non polymorphic records we need to care about field order as the
                // compiler assumes the order the fields occur in the type determines how
                // to access them
                let new_args = merge::merge_tuple_iter(l_args.iter().zip(r_args.iter()), |l, r| {
                    let opt_type = if !l.name.name_eq(&r.name) {
                        let err = TypeError::FieldMismatch(l.name.clone(), r.name.clone());
                        unifier.report_error(UnifyError::Other(err));
                        None
                    } else {
                        unifier.try_match(&l.typ, &r.typ)
                    };
                    opt_type.map(|typ| Field::new(l.name.clone(), typ))
                });
                let new_rest = unifier.try_match(l_rest, r_rest);
                Ok(merge::merge(
                    l_args,
                    new_args,
                    l_rest,
                    new_rest,
                    |fields, rest| Type::extend_row(l_types.clone(), fields, rest),
                ))
            } else {
                unify_rows(unifier, expected, actual)
            }
        }
        (&Type::Ident(ref id), &Type::Alias(ref alias)) if *id == alias.name => {
            Ok(Some(actual.clone()))
        }
        (&Type::Alias(ref alias), &Type::Ident(ref id)) if *id == alias.name => Ok(None),

        // Successful unification!
        (lhs, rhs) if lhs == rhs => Ok(None),

        // Last ditch attempt to unify the types expanding the aliases
        // (if the types are alias types).
        (_, _) => {
            let lhs = unifier
                .state
                .remove_aliases(expected)
                .map_err(UnifyError::Other)?;
            let rhs = unifier
                .state
                .remove_aliases(actual)
                .map_err(UnifyError::Other)?;

            match (&lhs, &rhs) {
                (&None, &None) => {
                    debug!("Unify error: {} <=> {}", expected, actual);
                    Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()))
                }
                (_, _) => {
                    let lhs = lhs.as_ref().unwrap_or(expected);
                    let rhs = rhs.as_ref().unwrap_or(actual);
                    // FIXME Maybe always return `None` here since the types before we removed the
                    // aliases are probably more specific.
                    unifier.try_match_res(lhs, rhs).map_err(|_err| {
                        // We failed to unify `lhs` and `rhs` at the spine. Replace that error with
                        // a mismatch between the aliases instead as that should be less verbose
                        // Example
                        // type A = | A Int
                        // type B = | B Float
                        // A <=> B
                        // Gives `A` != `B` instead of `| A Int` != `| B Float`
                        UnifyError::TypeMismatch(expected.clone(), actual.clone())
                    })
                }
            }
        }
    }
}

fn unify_app<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    l: &ArcType,
    l_args: &AppVec<ArcType>,
    r: &ArcType,
    r_args: &AppVec<ArcType>,
) -> Option<ArcType>
where
    U: Unifier<State<'a>, ArcType>,
{
    use std::cmp::Ordering::*;
    // Applications are curried `a b c d` == `((a b) c) d` we need to unify the last
    // argument which eachother followed by the second last etc.
    // If the number of arguments are not equal, the application with fewer arguments are
    // unified with the other type applied on its remaining arguments
    // a b c <> d e
    // Unifies:
    // c <> e
    // a b <> d
    match l_args.len().cmp(&r_args.len()) {
        Equal => {
            let new_type = unifier.try_match(l, r);
            let new_args =
                merge::merge_tuple_iter(l_args.iter().zip(r_args), |l, r| unifier.try_match(l, r));
            merge::merge(l, new_type, l_args, new_args, Type::app)
        }
        Less => {
            let offset = r_args.len() - l_args.len();

            let reduced_r = Type::app(r.clone(), r_args[..offset].iter().cloned().collect());
            let new_type = unifier.try_match(l, &reduced_r);

            let new_args = merge::merge_tuple_iter(l_args.iter().zip(&r_args[offset..]), |l, r| {
                unifier.try_match(l, r)
            });
            merge::merge(l, new_type, l_args, new_args, Type::app)
        }
        Greater => {
            let offset = l_args.len() - r_args.len();

            let reduced_l = Type::app(l.clone(), l_args[..offset].iter().cloned().collect());
            let new_type = unifier.try_match(&reduced_l, r);

            let new_args = merge::merge_tuple_iter(l_args[offset..].iter().zip(r_args), |l, r| {
                unifier.try_match(l, r)
            });
            merge::merge(r, new_type, r_args, new_args, Type::app)
        }
    }
}

fn gather_fields<'a, I, J, T>(
    l: I,
    r: J,
) -> (
    Vec<Field<Symbol, T>>,
    Vec<(&'a Field<Symbol, T>, &'a Field<Symbol, T>)>,
    Vec<Field<Symbol, T>>,
)
where
    I: Clone + IntoIterator<Item = &'a Field<Symbol, T>>,
    J: Clone + IntoIterator<Item = &'a Field<Symbol, T>>,
    T: Clone + 'a,
{
    let mut both = Vec::new();
    let mut missing_from_right = Vec::new();
    let mut l_iter = l.clone().into_iter();
    for l in l_iter.by_ref() {
        match r.clone().into_iter().find(|r| l.name.name_eq(&r.name)) {
            Some(r) => both.push((l, r)),
            None => missing_from_right.push(l.clone()),
        }
    }

    let mut r_iter = r.into_iter();
    let missing_from_left: Vec<_> = r_iter
        .by_ref()
        .filter(|r| l.clone().into_iter().all(|l| !l.name.name_eq(&r.name)))
        .cloned()
        .collect();
    (missing_from_left, both, missing_from_right)
}

/// Do unification between two rows. Each row is either `Type::ExtendRow` or `Type::EmptyRow`.
/// Two rows will unify successfully if all fields they have in common unifies and if either
/// record have additional fields not found in the other record, the other record can be extended.
/// A record can be extended if the `rest` part of `Type::ExtendRow` is a type variable in which
/// case that variable is unified with the missing fields.
fn unify_rows<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    l: &ArcType,
    r: &ArcType,
) -> Result<Option<ArcType>, Error<Symbol>>
where
    U: Unifier<State<'a>, ArcType>,
{
    let subs = unifier.state.subs;
    let (types_missing_from_left, types_both, types_missing_from_right) =
        gather_fields(l.type_field_iter(), r.type_field_iter());

    if !types_both.iter().all(|&(l, r)| l == r) {
        return Err(UnifyError::TypeMismatch(l.clone(), r.clone()));
    }

    let (missing_from_left, both, missing_from_right) = gather_fields(l.row_iter(), r.row_iter());

    let mut types: Vec<_> = types_both.iter().map(|pair| pair.0.clone()).collect();

    // Unify the fields that exists in both records
    let new_both = merge::merge_tuple_iter(both.iter().cloned(), |l, r| {
        unifier
            .try_match(&l.typ, &r.typ)
            .map(|typ| Field::new(l.name.clone(), typ))
    });

    // Pack all fields from both records into a single `Type::ExtendRow` value
    let mut fields: Vec<_> = match new_both {
        Some(fields) => fields,
        None => both.iter().map(|pair| pair.0.clone()).collect(),
    };

    // Unify the fields missing from the left and right record with the variable (that hopefully)
    // exists as the 'extension' in the other record
    // Example:
    // `{ x : Int | $0 } <=> `{ y : String | $1 }`
    // `Row (x : Int | Fresh var) <=> $1`
    // `Row (y : String | Fresh var 2) <=> $0`

    // This default `rest` value will only be used on errors, or if both fields has the same fields
    let mut r_iter = r.row_iter();
    for _ in r_iter.by_ref() {}
    let mut rest = r_iter.current_type().clone();

    // No need to do anything of no fields are missing
    if !missing_from_right.is_empty() {
        // If we attempt to unify with a non-polymorphic record we intercept the unification to
        // display a better error message
        match *rest {
            Type::EmptyRow => {
                let context = unifier
                    .state
                    .record_context
                    .as_ref()
                    .map_or(r, |p| &p.1)
                    .clone();
                let err = TypeError::MissingFields(
                    context,
                    missing_from_right
                        .into_iter()
                        .map(|field| field.name.clone())
                        .collect(),
                );
                unifier.report_error(UnifyError::Other(err));
            }
            _ => {
                rest = subs.new_var();
                let l_rest =
                    Type::extend_row(types_missing_from_right, missing_from_right, rest.clone());
                unifier.try_match(&l_rest, r_iter.current_type());
                types.extend(l_rest.type_field_iter().cloned());
                fields.extend(l_rest.row_iter().cloned());
            }
        }
    }

    // No need to do anything of no fields are missing
    if !missing_from_left.is_empty() {
        let mut l_iter = l.row_iter();
        for _ in l_iter.by_ref() {}

        match **l_iter.current_type() {
            Type::EmptyRow => {
                let context = unifier
                    .state
                    .record_context
                    .as_ref()
                    .map_or(l, |p| &p.0)
                    .clone();
                let err = TypeError::MissingFields(
                    context,
                    missing_from_left
                        .into_iter()
                        .map(|field| field.name.clone())
                        .collect(),
                );
                unifier.report_error(UnifyError::Other(err));
            }
            _ => {
                rest = subs.new_var();
                let r_rest =
                    Type::extend_row(types_missing_from_left, missing_from_left, rest.clone());
                unifier.try_match(l_iter.current_type(), &r_rest);
                types.extend(r_rest.type_field_iter().cloned());
                fields.extend(r_rest.row_iter().cloned());
            }
        }
    }

    Ok(Some(Type::extend_row(types, fields, rest)))
}

/// Attempt to unify two alias types.
/// To find a possible successful unification we walk through the alias expansions of `l` in an
/// attempt to find that `l` expands to the alias `r_id`
fn find_alias<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    l: ArcType,
    r_id: &SymbolRef,
) -> Result<Option<ArcType>, ()>
where
    U: Unifier<State<'a>, ArcType>,
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

fn find_alias_<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    mut l: ArcType,
    r_id: &SymbolRef,
) -> Result<Option<ArcType>, ()>
where
    U: Unifier<State<'a>, ArcType>,
{
    let mut did_alias = false;
    loop {
        l = match l.name() {
            Some(l_id) => {
                if let Some(l_id) = l.alias_ident() {
                    if unifier.state.reduced_aliases.iter().any(|id| id == l_id) {
                        return Err(());
                    }
                }
                debug!("Looking for alias reduction from `{}` to `{}`", l_id, r_id);
                if l_id == r_id {
                    // If the aliases matched before going through an alias there is no need to
                    // return a replacement type
                    return Ok(if did_alias { Some(l.clone()) } else { None });
                }
                did_alias = true;
                match resolve::remove_alias(unifier.state.env, &l) {
                    Ok(Some(typ)) => {
                        unifier
                            .state
                            .reduced_aliases
                            .push(l.alias_ident().expect("Alias").clone());
                        typ
                    }
                    Ok(None) => break,
                    Err(err) => {
                        unifier.report_error(UnifyError::Other(err.into()));
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
///
/// ```f#
/// type Test a = | Test a Int
/// type Test2 = Test String
///
/// // find_common_alias(Test2, Test 0) => Ok((Test String, Test 0))
/// // find_common_alias(Float, Test 0) => Ok((Float, Test 0))
/// ```
fn find_common_alias<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    expected: &ArcType,
    actual: &ArcType,
    through_alias: &mut bool,
) -> Result<(ArcType, ArcType), ()>
where
    U: Unifier<State<'a>, ArcType>,
{
    let mut l = expected.clone();
    if let Some(r_id) = actual.name() {
        l = match find_alias(unifier, l.clone(), r_id)? {
            None => l,
            Some(typ) => {
                *through_alias = true;
                return Ok((typ, actual.clone()));
            }
        };
    }
    let mut r = actual.clone();
    if let Some(l_id) = expected.name() {
        r = match find_alias(unifier, r.clone(), l_id)? {
            None => r,
            Some(typ) => {
                *through_alias = true;
                typ
            }
        };
    }
    Ok((l, r))
}

/// Replaces all instances `Type::Generic` in `typ` with fresh type variables (`Type::Variable`)
pub fn instantiate_generic_variables(
    named_variables: &mut FnvMap<Symbol, ArcType>,
    subs: &Substitution<ArcType>,
    constraints: &FnvMap<Symbol, Constraints<ArcType>>,
    typ: &ArcType,
) -> ArcType {
    use std::collections::hash_map::Entry;

    types::walk_move_type(typ.clone(), &mut |typ| match **typ {
        Type::Generic(ref generic) => {
            let var = match named_variables.entry(generic.id.clone()) {
                Entry::Vacant(entry) => {
                    let constraint = constraints.get(&generic.id).cloned();
                    entry
                        .insert(subs.new_constrained_var(
                            constraint.map(|constraint| (generic.id.clone(), constraint.clone())),
                        ))
                        .clone()
                }
                Entry::Occupied(entry) => entry.get().clone(),
            };

            let mut var = (*var).clone();
            if let Type::Variable(ref mut var) = var {
                var.kind = generic.kind.clone();
            }

            Some(ArcType::from(var))
        }
        _ => None,
    })
}

pub fn merge_signature(
    subs: &Substitution<ArcType>,
    variables: &mut ScopedMap<Symbol, ArcType>,
    level: u32,
    state: State,
    l: &ArcType,
    r: &ArcType,
) -> Result<ArcType, Errors<Error<Symbol>>> {
    let mut unifier = UnifierState {
        state: state,
        unifier: Merge {
            subs: subs,
            variables: variables,
            errors: Errors::new(),
            level: level,
        },
    };

    let typ = unifier.try_match(l, r);
    if unifier.unifier.errors.has_errors() {
        Err(unifier.unifier.errors)
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

struct Merge<'e> {
    subs: &'e Substitution<ArcType>,
    variables: &'e ScopedMap<Symbol, ArcType>,
    errors: Errors<Error<Symbol>>,
    level: u32,
}

impl<'a, 'e> Unifier<State<'a>, ArcType> for Merge<'e> {
    fn report_error(
        unifier: &mut UnifierState<Self>,
        error: UnifyError<ArcType, TypeError<Symbol>>,
    ) {
        unifier.unifier.errors.push(error);
    }

    fn try_match_res(
        unifier: &mut UnifierState<Self>,
        l: &ArcType,
        r: &ArcType,
    ) -> Result<Option<ArcType>, UnifyError<ArcType, TypeError<Symbol>>> {
        let subs = unifier.unifier.subs;
        // Retrieve the 'real' types by resolving
        let l = subs.real(l);
        let r = subs.real(r);
        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (&**l, &**r) {
            (&Type::Hole, _) => Ok(None),
            (&Type::Variable(ref l), &Type::Variable(ref r)) if l.id == r.id => Ok(None),
            (&Type::Generic(ref l_gen), &Type::Variable(ref r_var)) => {
                let left = match unifier.unifier.variables.get(&l_gen.id) {
                    Some(generic_bound_var) => {
                        match **generic_bound_var {
                            // The generic variable is defined outside the current scope. Use the
                            // type variable instantiated from the generic and unify with that
                            Type::Variable(ref var) if var.id < unifier.unifier.level => {
                                generic_bound_var
                            }
                            // `r_var` is outside the scope of the generic variable.
                            Type::Variable(ref var) if var.id > r_var.id => {
                                return Err(UnifyError::Other(
                                    TypeError::UnableToGeneralize(l_gen.id.clone()),
                                ));
                            }
                            _ => l,
                        }
                    }
                    None => l,
                };
                subs.union(|| unifier.state.fresh(), r_var, left)?;
                Ok(None)
            }
            (_, &Type::Variable(ref r)) => {
                subs.union(|| unifier.state.fresh(), r, l)?;
                Ok(None)
            }
            (&Type::Variable(ref l), _) => {
                subs.union(|| unifier.state.fresh(), l, r)?;
                Ok(Some(r.clone()))
            }
            _ => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                l.zip_match(r, unifier)
            }
        }
    }

    fn error_type(unifier: &mut UnifierState<Self>) -> Option<ArcType> {
        Some(unifier.unifier.subs.new_var())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use base::error::Errors;

    use unify::Error::*;
    use unify::unify;
    use substitution::Substitution;
    use base::kind::Kind;
    use base::types::{ArcType, Field, Type};
    use tests::*;

    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::init();
        let (x, y) = (intern("x"), intern("y"));
        let l: ArcType = Type::record(
            vec![],
            vec![
                Field::new(x.clone(), Type::int()),
                Field::new(y.clone(), Type::string()),
            ],
        );
        let r = Type::record(
            vec![],
            vec![
                Field::new(x.clone(), Type::string()),
                Field::new(y.clone(), Type::int()),
            ],
        );
        let subs = Substitution::new(Kind::typ());
        let env = MockEnv;
        let state = State::new(&env, &subs);
        let result = unify(&subs, state, &l, &r);
        assert_eq!(
            result,
            Err(Errors::from(vec![
                TypeMismatch(Type::int(), Type::string()),
                TypeMismatch(Type::string(), Type::int()),
            ]))
        );
    }

    #[test]
    fn unify_row_polymorphism() {
        let _ = ::env_logger::init();

        let env = MockEnv;
        let subs = Substitution::new(Kind::typ());
        let state = State::new(&env, &subs);

        let x = Field::new(intern("x"), Type::int());
        let y = Field::new(intern("y"), Type::int());
        let l: ArcType = Type::poly_record(vec![], vec![x.clone()], subs.new_var());
        let r = Type::poly_record(vec![], vec![y.clone()], subs.new_var());

        match unify(&subs, state, &l, &r) {
            Ok(result) => {
                // Get the row variable at the end of the resulting type so we can compare the types
                let mut iter = result.row_iter();
                for _ in iter.by_ref() {}
                let row_variable = iter.current_type().clone();
                let expected = Type::poly_record(vec![], vec![x.clone(), y.clone()], row_variable);
                assert_eq!(result, expected);
            }
            Err(err) => ice!("{}", err),
        }
    }
}
