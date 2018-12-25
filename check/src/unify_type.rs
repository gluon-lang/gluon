use std::{borrow::Cow, fmt, mem};

use base::error::Errors;
use base::fnv::FnvMap;
use base::kind::ArcKind;
use base::merge;
use base::resolve::{self, Error as ResolveError};
use base::symbol::{Symbol, SymbolRef};
use base::types::{
    self, AppVec, ArcType, ArgType, BuiltinType, Field, Filter, Generic, Skolem, Type, TypeCache,
    TypeEnv, TypeFormatter, TypeVariable,
};

use substitution::{Substitutable, Substitution, Variable, VariableFactory};
use unify;
use unify::{Error as UnifyError, GenericVariant, Unifiable, Unifier};

use smallvec::SmallVec;

pub type Result<T, E = UnifyError<ArcType, TypeError<Symbol>>> = ::std::result::Result<T, E>;

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
    type_cache: &'a TypeCache<Symbol, ArcType>,
    pub in_alias: bool,
}

impl<'a> State<'a> {
    pub fn new(
        env: &'a (TypeEnv + 'a),
        subs: &'a Substitution<ArcType>,
        type_cache: &'a TypeCache<Symbol, ArcType>,
    ) -> State<'a> {
        State {
            env,
            reduced_aliases: Vec::new(),
            subs,
            type_cache,
            record_context: None,
            in_alias: false,
        }
    }

    fn remove_aliases(
        &mut self,
        subs: &Substitution<ArcType>,
        typ: &ArcType,
    ) -> Result<Option<ArcType>, TypeError<Symbol>> {
        if let Some(alias_id) = typ.alias_ident() {
            if self.reduced_aliases.iter().any(|name| name == alias_id) {
                return Err(TypeError::SelfRecursiveAlias(alias_id.clone()));
            }
            self.reduced_aliases.push(alias_id.clone());
        }

        match resolve::remove_alias(&self.env, typ)? {
            Some(mut typ) => {
                loop {
                    typ = types::walk_move_type(typ.clone(), &mut |typ| match **typ {
                        Type::Forall(_, _, None) => {
                            let typ = new_skolem_scope(subs, typ);
                            Some(typ)
                        }
                        _ => None,
                    });
                    if let Some(alias_id) = typ.alias_ident() {
                        if self.reduced_aliases.iter().any(|name| name == alias_id) {
                            return Err(TypeError::SelfRecursiveAlias(alias_id.clone()));
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
    SelfRecursiveAlias(I),
    UnableToGeneralize(I),
    MissingFields(ArcType<I>, Vec<I>),
}

impl From<ResolveError> for TypeError<Symbol> {
    fn from(error: ResolveError) -> TypeError<Symbol> {
        match error {
            ResolveError::UndefinedType(id) => TypeError::UndefinedType(id),
            ResolveError::SelfRecursiveAlias(id) => TypeError::SelfRecursiveAlias(id),
        }
    }
}

impl<I> fmt::Display for TypeError<I>
where
    I: fmt::Display + AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let filter = self.make_filter();
        self.filter_fmt(&*filter, f)
    }
}

pub fn similarity_filter<'a, I>(typ: &'a ArcType<I>, fields: &'a [I]) -> Box<Fn(&I) -> Filter + 'a>
where
    I: AsRef<str>,
{
    let mut field_similarity = typ
        .type_field_iter()
        .map(|field| &field.name)
        .chain(typ.row_iter().map(|field| &field.name))
        .map(|field_in_type| {
            let similarity = fields
                .iter()
                .map(|missing_field| {
                    ::strsim::jaro_winkler(missing_field.as_ref(), field_in_type.as_ref())
                })
                .max_by(|l, r| l.partial_cmp(&r).unwrap())
                .expect("At least one missing field");
            (field_in_type, (similarity * 1000000.) as i32)
        })
        .collect::<Vec<_>>();
    field_similarity.sort_by_key(|t| ::std::cmp::Reverse(t.1));

    Box::new(move |field: &I| {
        // Keep the fields that were missing as-is (with full types)
        if fields.iter().any(|f| f.as_ref() == field.as_ref()) {
            Filter::Retain
        } else if field_similarity
            .iter()
            .take(3)
            .any(|t| t.0.as_ref() == field.as_ref())
        {
            Filter::RetainKey
        } else {
            Filter::Drop
        }
    })
}

impl<I> TypeError<I>
where
    I: fmt::Display + AsRef<str>,
{
    pub fn make_filter<'a>(&'a self) -> Box<Fn(&I) -> Filter + 'a> {
        match *self {
            TypeError::FieldMismatch(ref l, ref r) => Box::new(move |field| {
                if [l, r].iter().any(|f| f.as_ref() == field.as_ref()) {
                    Filter::Retain
                } else {
                    Filter::Drop
                }
            }),
            TypeError::UndefinedType(_) => Box::new(|_| Filter::Retain),
            TypeError::SelfRecursiveAlias(_) => Box::new(|_| Filter::Retain),
            TypeError::UnableToGeneralize(_) => Box::new(|_| Filter::Retain),
            TypeError::MissingFields(ref typ, ref fields) => similarity_filter(typ, fields),
        }
    }

    pub fn filter_fmt(&self, filter: &Fn(&I) -> Filter, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeError::FieldMismatch(ref l, ref r) => write!(
                f,
                "Row labels do not match.\n    Expected: {}\n    Found: {}",
                l, r
            ),
            TypeError::UndefinedType(ref id) => write!(f, "Type `{}` is not defined.", id),
            TypeError::SelfRecursiveAlias(ref id) => write!(
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
                write!(
                    f,
                    "The type `{}` lacks the following fields: ",
                    TypeFormatter::new(typ).filter(filter)
                )?;
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

    fn get_id(&self) -> Option<u32> {
        match **self {
            Type::Variable(ref var) => Some(var.id),
            Type::Skolem(ref skolem) => Some(skolem.id),
            _ => None,
        }
    }

    fn traverse<'a, F>(&'a self, f: &mut F)
    where
        F: types::Walker<'a, Self>,
    {
        types::walk_type_(self, f)
    }

    fn instantiate(&self, subs: &Substitution<Self>) -> Self {
        new_skolem_scope(subs, self).instantiate_generics(&mut FnvMap::default())
    }

    fn on_union(&self) -> Option<&Self> {
        unpack_single_forall(self)
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
        UnifierState<'a, U>: Unifier<State<'a>, Self>,
    {
        let reduced_aliases = unifier.state.reduced_aliases.len();
        let (l_temp, r_temp);
        let (mut l, mut r) = (self, other);
        let mut through_alias = false;
        match find_common_alias(unifier, self, other, &mut through_alias) {
            Ok((l2, r2)) => {
                if through_alias {
                    let old_in_alias = unifier.state.in_alias;
                    unifier.state.in_alias = true;
                    let result = unifier.try_match_res(&l2, &r2);
                    unifier.state.in_alias = old_in_alias;
                    unifier.state.reduced_aliases.truncate(reduced_aliases);
                    return result;
                }
                l_temp = l2;
                r_temp = r2;
                l = &l_temp;
                r = &r_temp;
            }
            Err(()) => (),
        }
        let result = do_zip_match(unifier, l, r)
            .map(|mut unified_type| {
                // Return polymorphic rows even if we have gone through aliases as they
                // can very well be more specific after the row has been extended
                // Should have a better way to handle this though...
                let is_polymorphic_row = |typ: &ArcType| -> bool {
                    let mut iter = typ.row_iter();
                    for _ in iter.by_ref() {}
                    **unifier.state.subs.real(iter.current_type()) != Type::EmptyRow
                };
                // If the match was done through an alias the unified type is likely less precise than
                // `self` or `other`.
                // So just return `None` which means `self` is used as the type if necessary
                if through_alias && !unified_type.as_ref().map_or(false, is_polymorphic_row) {
                    unified_type.take();
                }
                unified_type
            })
            .map_err(|err| {
                // Use the aliased types if we  the
                if through_alias {
                    match err {
                        unify::Error::TypeMismatch(..) => {
                            unify::Error::TypeMismatch(self.clone(), other.clone())
                        }
                        _ => err,
                    }
                } else {
                    err
                }
            });
        unifier.state.reduced_aliases.truncate(reduced_aliases);
        result
    }

    fn error_type(state: &State<'a>) -> Self {
        state.type_cache.error()
    }
}

fn do_zip_match<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    expected: &ArcType,
    actual: &ArcType,
) -> Result<Option<ArcType>, Error<Symbol>>
where
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
{
    debug!("Unifying:\n{} <=> {}", expected, actual);
    match (&**expected, &**actual) {
        (&Type::Error, _) => Ok(Some(actual.clone())),

        (_, &Type::Error) => Ok(None),

        (
            &Type::Function(l_arg_type, ref l_arg, ref l_ret),
            &Type::Function(r_arg_type, ref r_arg, ref r_ret),
        ) if l_arg_type == r_arg_type => {
            let arg = unifier.try_match(l_arg, r_arg);
            let ret = unifier.try_match(l_ret, r_ret);
            Ok(merge::merge(l_arg, arg, l_ret, ret, |arg, ret| {
                ArcType::from(Type::Function(l_arg_type, arg, ret))
            }))
        }

        (
            &Type::Function(ArgType::Explicit, ref l_arg, ref l_ret),
            &Type::App(ref r, ref r_args),
        ) => {
            let l_args = collect![l_arg.clone(), l_ret.clone()];
            unify_app(
                unifier,
                &Type::builtin(BuiltinType::Function),
                &l_args,
                r,
                r_args,
            )
            .map_err(|_| UnifyError::TypeMismatch(expected.clone(), actual.clone()))
        }

        (
            &Type::App(ref l, ref l_args),
            &Type::Function(ArgType::Explicit, ref r_arg, ref r_ret),
        ) => {
            let r_args = collect![r_arg.clone(), r_ret.clone()];
            unify_app(
                unifier,
                l,
                l_args,
                &Type::builtin(BuiltinType::Function),
                &r_args,
            )
            .map_err(|_| UnifyError::TypeMismatch(expected.clone(), actual.clone()))
        }

        (&Type::App(ref l, ref l_args), &Type::App(ref r, ref r_args)) => {
            unify_app(unifier, l, l_args, r, r_args)
                .map_err(|_| UnifyError::TypeMismatch(expected.clone(), actual.clone()))
        }

        (&Type::Variant(ref l_row), &Type::Variant(ref r_row)) => {
            // Store the current variants so that they can be used when displaying field errors
            let previous = mem::replace(
                &mut unifier.state.record_context,
                Some((expected.clone(), actual.clone())),
            );
            let result = unifier
                .try_match(l_row, r_row)
                .map(|row| ArcType::from(Type::Variant(row)));
            unifier.state.record_context = previous;
            Ok(result)
        }

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

        (&Type::Effect(ref l_row), &Type::Effect(ref r_row)) => {
            // Store the current variants so that they can be used when displaying field errors
            let previous = mem::replace(
                &mut unifier.state.record_context,
                Some((expected.clone(), actual.clone())),
            );
            let result = unifier
                .try_match(l_row, r_row)
                .map(|row| ArcType::from(Type::Effect(row)));
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
            if l_args.len() == r_args.len()
                && l_args
                    .iter()
                    .zip(r_args)
                    .all(|(l, r)| l.name.name_eq(&r.name))
                && l_types == r_types
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

                {
                    use std::cmp::Ordering::*;
                    match l_args.len().cmp(&r_args.len()) {
                        Equal => (),
                        Less => {
                            let context = unifier
                                .state
                                .record_context
                                .as_ref()
                                .map_or(actual, |p| &p.1)
                                .clone();
                            let err = TypeError::MissingFields(
                                context,
                                r_args[l_args.len()..]
                                    .iter()
                                    .map(|field| field.name.clone())
                                    .collect(),
                            );
                            unifier.report_error(UnifyError::Other(err));
                        }
                        Greater => {
                            let context = unifier
                                .state
                                .record_context
                                .as_ref()
                                .map_or(expected, |p| &p.0)
                                .clone();
                            let err = TypeError::MissingFields(
                                context,
                                l_args[r_args.len()..]
                                    .iter()
                                    .map(|field| field.name.clone())
                                    .collect(),
                            );
                            unifier.report_error(UnifyError::Other(err));
                        }
                    }
                }

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

        (&Type::ExtendRow { .. }, &Type::EmptyRow) | (&Type::EmptyRow, &Type::ExtendRow { .. }) => {
            unify_rows(unifier, expected, actual)
        }

        (&Type::Ident(ref id), &Type::Alias(ref alias)) if *id == alias.name => {
            Ok(Some(actual.clone()))
        }

        (&Type::Alias(ref alias), &Type::Ident(ref id)) if *id == alias.name => Ok(None),

        (&Type::Forall(ref params, _, Some(ref vars)), &Type::Forall(_, _, Some(_))) => {
            let mut named_variables = FnvMap::default();

            if unifier.state.in_alias {
                let l = expected.skolemize(&mut named_variables);
                named_variables.clear();
                let r = actual.skolemize(&mut named_variables);

                Ok(unifier.try_match_res(&l, &r)?.map(|inner_type| {
                    reconstruct_forall(unifier.state.subs, params, inner_type, vars)
                }))
            } else {
                let mut expected_iter = expected.forall_scope_iter();
                named_variables.extend(expected_iter.by_ref().map(|(l_param, l_var)| {
                    let l_var = l_var.as_variable().unwrap();
                    (
                        l_param.id.clone(),
                        Type::skolem(Skolem {
                            name: l_param.id.clone(),
                            id: l_var.id,
                            kind: l_var.kind.clone(),
                        }),
                    )
                }));
                let l = expected_iter.typ.skolemize(&mut named_variables);

                named_variables.clear();
                let mut actual_iter = actual.forall_scope_iter();
                named_variables.extend(expected_iter.by_ref().zip(actual_iter.by_ref()).map(
                    |((_, l_var), (r_param, r_var))| {
                        let l_var = l_var.as_variable().unwrap();
                        let r_var = r_var.as_variable().unwrap();
                        (
                            r_param.id.clone(),
                            Type::skolem(Skolem {
                                name: r_param.id.clone(),
                                id: l_var.id,
                                kind: r_var.kind.clone(),
                            }),
                        )
                    },
                ));
                let r = actual_iter.typ.skolemize(&mut named_variables);

                Ok(unifier.try_match_res(&l, &r)?.map(|inner_type| {
                    reconstruct_forall(unifier.state.subs, params, inner_type, vars)
                }))
            }
        }

        (&Type::Skolem(ref l), &Type::Skolem(ref r)) if r.id == l.id => Ok(None),

        // Successful unification!
        (lhs, rhs) if lhs == rhs => Ok(None),

        // Last ditch attempt to unify the types expanding the aliases
        // (if the types are alias types).
        (_, _) => {
            let subs = unifier.state.subs;
            let lhs_base = unifier
                .state
                .remove_aliases(subs, expected)
                .map_err(UnifyError::Other)?;
            let rhs_base = unifier
                .state
                .remove_aliases(subs, actual)
                .map_err(UnifyError::Other)?;

            match (&lhs_base, &rhs_base) {
                (&None, &None) => {
                    debug!("Unify error: {:?} <=> {:?}", expected, actual);
                    Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()))
                }
                (_, _) => {
                    let lhs = lhs_base.as_ref().unwrap_or(expected);
                    let rhs = rhs_base.as_ref().unwrap_or(actual);

                    let old_in_alias = unifier.state.in_alias;
                    unifier.state.in_alias = true;

                    let result = unifier
                        .try_match_res(lhs, rhs)
                        .map(|typ| {
                            if unifier.allow_returned_type_replacement() || typ.is_none() {
                                // Always ignore the type returned from try_match_res since it will be less specialized than
                                // `lhs` or `rhs`. If `lhs` is an alias we return `None` since `lhs` will be chosen if necessary anyway
                                // otherwise if `lhs` is not an alias then `rhs` must have been so chose `rhs/actual`
                                if lhs_base.is_some() {
                                    None
                                } else {
                                    Some(actual.clone())
                                }
                            } else {
                                typ
                            }
                        })
                        .map_err(|_err| {
                            // We failed to unify `lhs` and `rhs` at the spine. Replace that error with
                            // a mismatch between the aliases instead as that should be less verbose
                            // Example
                            // type A = | A Int
                            // type B = | B Float
                            // A <=> B
                            // Gives `A` != `B` instead of `| A Int` != `| B Float`
                            UnifyError::TypeMismatch(expected.clone(), actual.clone())
                        });

                    unifier.state.in_alias = old_in_alias;

                    result
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
) -> Result<Option<ArcType>, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
{
    use std::cmp::Ordering::*;
    // Applications are curried `a b c d` == `((a b) c) d` we need to unify the last
    // argument which each other followed by the second last etc.
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
            Ok(merge::merge(l, new_type, l_args, new_args, Type::app))
        }
        Less => {
            let offset = r_args.len() - l_args.len();

            let reduced_r = Type::app(r.clone(), r_args[..offset].iter().cloned().collect());
            let new_type = match unifier.try_match_res(l, &reduced_r) {
                Ok(new_type) => new_type,
                Err(_err) => {
                    return Err(());
                }
            };

            let new_args = merge::merge_tuple_iter(l_args.iter().zip(&r_args[offset..]), |l, r| {
                unifier.try_match(l, r)
            });
            Ok(merge::merge(l, new_type, l_args, new_args, Type::app))
        }
        Greater => {
            let offset = l_args.len() - r_args.len();

            let reduced_l = Type::app(l.clone(), l_args[..offset].iter().cloned().collect());
            let new_type = match unifier.try_match_res(&reduced_l, r) {
                Ok(new_type) => new_type,
                Err(_err) => {
                    return Err(());
                }
            };

            let new_args = merge::merge_tuple_iter(l_args[offset..].iter().zip(r_args), |l, r| {
                unifier.try_match(l, r)
            });
            Ok(merge::merge(r, new_type, r_args, new_args, Type::app))
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
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
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

fn resolve_application<'t>(typ: &'t ArcType, subs: &'t Substitution<ArcType>) -> Option<ArcType> {
    match **typ {
        Type::App(ref f, ref a) => resolve_application(f, subs).map(|f| Type::app(f, a.clone())),
        Type::Variable(_) => {
            let typ = subs.real(typ);
            match **typ {
                Type::Variable(_) => None,
                _ => Some(resolve_application(typ, subs).unwrap_or_else(|| typ.clone())),
            }
        }
        _ => None,
    }
}

#[derive(Debug)]
enum FoundAlias {
    Root(ArcType),
    Found(ArcType),
    AlreadyDone,
}

/// Attempt to unify two alias types.
/// To find a possible successful unification we walk through the alias expansions of `l` in an
/// attempt to find that `l` expands to the alias `r_id`
fn find_alias<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    l: ArcType,
    r_id: &SymbolRef,
) -> Result<FoundAlias, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
{
    let reduced_aliases = unifier.state.reduced_aliases.len();
    let result = find_alias_(unifier, l, r_id);
    match result {
        Ok(FoundAlias::Root(_)) | Ok(FoundAlias::Found(_)) => (),
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
) -> Result<FoundAlias, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
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
                    return Ok(if did_alias {
                        FoundAlias::Found(l.clone())
                    } else {
                        FoundAlias::AlreadyDone
                    });
                }
                match resolve::remove_alias(unifier.state.env, &l) {
                    Ok(Some(typ)) => {
                        did_alias = true;
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
    Ok(if did_alias {
        FoundAlias::Root(l)
    } else {
        FoundAlias::AlreadyDone
    })
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
    UnifierState<'a, U>: Unifier<State<'a>, ArcType>,
{
    // If the spine of the application consists of type variables we must first resolve those
    // before trying the alias as the resolve module does not know about type varaibles
    let mut r = resolve_application(actual, unifier.state.subs).unwrap_or_else(|| actual.clone());
    let mut l =
        resolve_application(expected, unifier.state.subs).unwrap_or_else(|| expected.clone());
    let mut l_root = None;
    let reduced_aliases_len = unifier.state.reduced_aliases.len();
    if let Some(r_id) = r.name() {
        l = match find_alias(unifier, l.clone(), r_id)? {
            FoundAlias::Root(root) => {
                l_root = Some(root);
                l
            }
            FoundAlias::AlreadyDone => l,
            FoundAlias::Found(typ) => {
                *through_alias = true;
                return Ok((typ, actual.clone()));
            }
        };
    }

    // Avoid triggering invalid self recursion checks from anything that the first find did
    let mut saved_aliases: SmallVec<[_; 5]> = unifier
        .state
        .reduced_aliases
        .drain(reduced_aliases_len..)
        .collect();

    let result = if let Some(l_id) = l.name() {
        Some(find_alias(unifier, r.clone(), l_id)?)
    } else {
        None
    };
    if let Some(result) = result {
        r = match result {
            FoundAlias::Root(root) => {
                *through_alias = true;
                if let Some(l_root) = l_root {
                    l = l_root;
                }
                root
            }
            FoundAlias::AlreadyDone => {
                saved_aliases.clear();
                r
            }
            FoundAlias::Found(typ) => {
                *through_alias = true;
                typ
            }
        };
    }

    unifier.state.reduced_aliases.extend(saved_aliases);

    Ok((l, r))
}

// HACK
// Currently the substitution assumes that once a variable has been unified to a
// concrete type it cannot be unified to another type later.
//
// This is true in ever case except `forall a . a`, while `forall a . a` looks
// like a concrete type it can actually turn into just an unknown type variable
// breaking this assumption (by replacing `a` with the bound unkown variable).
//
// So to guard against this we unpack the forall into the unknown variable which
// might cause some valid programs fail to compile but should not let invalid
// programs compile
fn unpack_single_forall(l: &ArcType) -> Option<&ArcType> {
    match **l {
        Type::Forall(ref params, ref l_inner, Some(ref vars)) if params.len() == 1 => {
            match **l_inner {
                Type::Skolem(ref skolem) if skolem.name == params[0].id => Some(&vars[0]),
                // FIXME
                // Since `Type::Forall` contains `Some` the `Generic` should have
                // been skolemized
                Type::Generic(ref gen) if gen.id == params[0].id => Some(&vars[0]),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Replaces all instances `Type::Generic` in `typ` with fresh type variables (`Type::Variable`)
pub fn new_skolem_scope(subs: &Substitution<ArcType>, typ: &ArcType) -> ArcType {
    new_skolem_scope_(subs, typ).unwrap_or_else(|| typ.clone())
}

fn new_skolem_scope_(subs: &Substitution<ArcType>, typ: &ArcType) -> Option<ArcType> {
    if let Some((arg_type, arg, ret)) = typ.as_function_with_type() {
        return new_skolem_scope_(subs, ret)
            .map(|ret| Type::function_type(arg_type, Some(arg.clone()), ret));
    }

    match **typ {
        Type::Forall(ref params, ref inner_type, None) => {
            let mut skolem = Vec::new();
            for param in params {
                let var = subs.new_var_fn(|id| {
                    Type::variable(TypeVariable {
                        id,
                        kind: param.kind.clone(),
                    })
                });
                skolem.push(var.clone());
            }
            Some(ArcType::from(Type::Forall(
                params.clone(),
                new_skolem_scope_(subs, inner_type).unwrap_or_else(|| inner_type.clone()),
                Some(skolem),
            )))
        }
        _ => types::walk_move_type_opt(
            typ,
            &mut types::ControlVisitation(|typ: &ArcType| new_skolem_scope_(subs, typ)),
        ),
    }
}

pub fn top_skolem_scope(subs: &Substitution<ArcType>, typ: &ArcType) -> ArcType {
    if let Type::Forall(ref params, ref inner_type, None) = **typ {
        let skolem = params.iter().map(|_| subs.new_var()).collect();
        ArcType::from(Type::Forall(
            params.clone(),
            inner_type.clone(),
            Some(skolem),
        ))
    } else {
        typ.clone()
    }
}

/// Performs subsumption between `l` and `r` (`r` is-a `l`)
pub fn subsumes(
    subs: &Substitution<ArcType>,
    state: State,
    l: &ArcType,
    r: &ArcType,
) -> Result<ArcType, (ArcType, Errors<Error<Symbol>>)> {
    debug!("Subsume {} <=> {}", l, r);
    let mut unifier = UnifierState {
        state: state,
        unifier: Subsume {
            subs: subs,
            errors: Errors::new(),
            allow_returned_type_replacement: true,
        },
    };

    let typ = unifier.try_match(l, r);
    if unifier.unifier.errors.has_errors() {
        Err((typ.unwrap_or_else(|| l.clone()), unifier.unifier.errors))
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

struct Subsume<'e> {
    subs: &'e Substitution<ArcType>,
    errors: Errors<Error<Symbol>>,
    allow_returned_type_replacement: bool,
}

impl<'a, 'e> UnifierState<'a, Subsume<'e>> {
    fn subsume_check(&mut self, l: &ArcType, r: &ArcType) -> Option<ArcType> {
        let l = new_skolem_scope(self.unifier.subs, &l);
        let l_orig = &l;
        let l = l.skolemize(&mut FnvMap::default());
        let typ = self.try_match(&l, r);

        typ.or(if l_orig.forall_params_vars().next().is_some() {
            Some(l.clone())
        } else {
            None
        })
        .map(|typ| {
            self.unifier.allow_returned_type_replacement = false;
            typ.with_forall(l_orig)
        })
    }

    fn subsume_check_rho(&mut self, l: &ArcType, r: &ArcType) -> Option<ArcType> {
        self.try_match(l, r)
    }

    fn subsume_check_function(
        &mut self,
        arg_l: &ArcType,
        ret_l: &ArcType,
        arg_r: &ArcType,
        ret_r: &ArcType,
    ) -> Option<ArcType> {
        let arg = self.subsume_check(arg_r, arg_l);
        let ret = self.subsume_check_rho(ret_l, ret_r);
        merge::merge(arg_l, arg, ret_l, ret, |arg, ret| {
            Type::function(vec![arg], ret)
        })
    }

    fn unify_function(&mut self, actual: &ArcType) -> (ArcType, ArcType) {
        let subs = self.state.subs;
        let actual = match self.state.remove_aliases(subs, &actual) {
            Ok(t) => t.map_or_else(|| Cow::Borrowed(actual), Cow::Owned),
            Err(err) => {
                self.report_error(UnifyError::Other(err));
                Cow::Borrowed(actual)
            }
        };
        match actual.as_explicit_function() {
            Some((arg, ret)) => return (arg.clone(), ret.clone()),
            None => (),
        }
        let arg = subs.new_var();
        let ret = subs.new_var();
        let f = self
            .state
            .type_cache
            .function(Some(arg.clone()), ret.clone());
        if let Err(errors) = unify::unify(subs, self.state.clone(), &f, &actual) {
            for err in errors {
                self.report_error(err);
            }
        }
        (arg, ret)
    }
}

impl<'a, 'e> Unifier<State<'a>, ArcType> for UnifierState<'a, Subsume<'e>> {
    fn report_error(&mut self, error: UnifyError<ArcType, TypeError<Symbol>>) {
        debug!("Error {}", error);
        self.unifier.errors.push(error);
    }

    fn allow_returned_type_replacement(&self) -> bool {
        self.unifier.allow_returned_type_replacement
    }

    fn try_match_res(
        &mut self,
        l: &ArcType,
        r: &ArcType,
    ) -> Result<Option<ArcType>, UnifyError<ArcType, TypeError<Symbol>>> {
        let subs = self.unifier.subs;
        // Retrieve the 'real' types by resolving
        let l = subs.real(l);
        let r = subs.real(r);
        debug!("{} <=> {}", l, r);
        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (&**l, &**r) {
            (&Type::Hole, _) => Ok(Some(r.clone())),
            (&Type::Variable(ref l), &Type::Variable(ref r)) if l.id == r.id => Ok(None),

            (_, &Type::Forall(ref params, ref r, _)) => {
                let mut variables = params
                    .iter()
                    .map(|param| (param.id.clone(), subs.new_var()))
                    .collect();
                let r = r.instantiate_generics(&mut variables);
                self.try_match_res(l, &r)
            }

            (_, &Type::Variable(ref r)) => {
                debug!("Union merge {} <> {}", l, r);
                subs.union(r, l)?;
                Ok(None)
            }
            (&Type::Variable(ref l), _) => {
                debug!("Union merge {} <> {}", l, r);
                subs.union(l, r)?;
                Ok(Some(r.clone()))
            }

            (&Type::Forall(_, _, _), _) => Ok(self.subsume_check(l, r)),

            _ if l.as_explicit_function().is_some() => {
                let (arg_l, ret_l) = l.as_explicit_function().unwrap();
                let (arg_r, ret_r) = self.unify_function(r);
                Ok(self.subsume_check_function(arg_l, ret_l, &arg_r, &ret_r))
            }
            _ if r.as_explicit_function().is_some() => {
                let (arg_r, ret_r) = r.as_explicit_function().unwrap();
                let (arg_l, ret_l) = self.unify_function(l);
                Ok(self.subsume_check_function(&arg_l, &ret_l, arg_r, ret_r))
            }
            _ => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                l.zip_match(r, self)
            }
        }
    }

    fn error_type(&self) -> ArcType {
        ArcType::error_type(&self.state)
    }
}

fn reconstruct_forall(
    subs: &Substitution<ArcType>,
    params: &[Generic<Symbol>],
    inner_type: ArcType,
    vars: &[ArcType],
) -> ArcType {
    use substitution::is_variable_unified;

    let mut new_params = Vec::new();
    let mut new_vars = Vec::new();
    for (param, var) in params
        .iter()
        .zip(vars)
        .filter(|&(_, var)| !is_variable_unified(subs, var))
    {
        new_params.push(param.clone());
        new_vars.push(var.clone());
    }
    Type::forall_with_vars(new_params, inner_type, Some(new_vars))
}

#[cfg(test)]
mod tests {
    use super::*;
    use base::error::Errors;

    use base::kind::Kind;
    use base::types::{ArcType, Field, Type};
    use substitution::Substitution;
    use tests::*;
    use unify::unify;
    use unify::Error::*;

    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::try_init();
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
        let env = MockEnv;
        let type_cache = TypeCache::new();
        let subs = Substitution::new(Kind::typ());
        let state = State::new(&env, &subs, &type_cache);
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
        let _ = ::env_logger::try_init();

        let env = MockEnv;
        let type_cache = TypeCache::new();
        let subs = Substitution::new(Kind::typ());
        let state = State::new(&env, &subs, &type_cache);

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
