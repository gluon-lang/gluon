use std::{borrow::Cow, fmt, mem};

use crate::base::{
    ast,
    error::Errors,
    fnv::FnvMap,
    kind::ArcKind,
    merge, pos,
    resolve::{self, Error as ResolveError},
    symbol::{Symbol, SymbolRef},
    types::{AsId,
        self, walk_type, AppVec, ArgType, Field, Filter, SharedInterner, Skolem, Type, TypeContext,
        TypeEnv, TypeExt, TypeFormatter, TypePtr, TypeVariable,
    },
};

use crate::{
    substitution::{Substitutable, Substitution, Variable, VariableFactory},
    typ::{Flags, RcType},
    unify::{self, Error as UnifyError, Unifiable, Unifier},
};

use smallvec::SmallVec;

pub type Result<T, E = UnifyError<TypeError<Symbol, RcType>, RcType>> = ::std::result::Result<T, E>;

impl VariableFactory for ArcKind {
    type Variable = TypeVariable;
    fn new(&self, id: u32) -> TypeVariable {
        TypeVariable {
            id: id,
            kind: self.clone(),
        }
    }
}

pub type Error<I, T = RcType> = UnifyError<TypeError<I, T>, T>;

#[derive(Clone)]
pub struct State<'a> {
    env: &'a (dyn TypeEnv<Type = RcType> + 'a),
    /// A stack of which aliases are currently expanded. Used to determine when an alias is
    /// recursively expanded in which case the unification fails.
    reduced_aliases: Vec<Symbol>,
    subs: &'a Substitution<RcType>,
    record_context: Option<(RcType, RcType)>,
    pub in_alias: bool,
    refinement: bool,
}

impl<'a> State<'a> {
    pub fn new(
        env: &'a (dyn TypeEnv<Type = RcType> + 'a),
        subs: &'a Substitution<RcType>,
    ) -> State<'a> {
        State::with_refinement(env, subs, false)
    }

    pub fn with_refinement(
        env: &'a (dyn TypeEnv<Type = RcType> + 'a),
        subs: &'a Substitution<RcType>,
        refinement: bool,
    ) -> State<'a> {
        State {
            env,
            reduced_aliases: Vec::new(),
            subs,
            record_context: None,
            in_alias: false,
            refinement,
        }
    }

    fn remove_aliases(
        &mut self,
        mut subs: &Substitution<RcType>,
        typ: &RcType,
    ) -> Result<Option<RcType>, TypeError<Symbol, RcType>> {
        if let Some(alias_id) = typ.alias_ident() {
            if self.reduced_aliases.iter().any(|name| name == alias_id) {
                return Err(TypeError::SelfRecursiveAlias(alias_id.clone()));
            }
            self.reduced_aliases.push(alias_id.clone());
        }

        match resolve::remove_alias(&self.env, &mut subs, typ)? {
            Some(mut typ) => {
                loop {
                    if let Some(alias_id) = typ.alias_ident() {
                        if self.reduced_aliases.iter().any(|name| name == alias_id) {
                            return Err(TypeError::SelfRecursiveAlias(alias_id.clone()));
                        }
                        self.reduced_aliases.push(alias_id.clone());
                    }

                    match resolve::remove_alias(&self.env, &mut subs, &typ)? {
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

#[derive(Debug, Eq, PartialEq, Hash, Clone, Functor)]
pub enum TypeError<I, T> {
    UndefinedType(I),
    FieldMismatch(I, I),
    SelfRecursiveAlias(I),
    UnableToGeneralize(I),
    MissingFields(T, Vec<I>),
    EscapingSkolem(I),
}

impl<T> From<ResolveError> for TypeError<Symbol, T> {
    fn from(error: ResolveError) -> TypeError<Symbol, T> {
        match error {
            ResolveError::UndefinedType(id) => TypeError::UndefinedType(id),
            ResolveError::SelfRecursiveAlias(id) => TypeError::SelfRecursiveAlias(id),
        }
    }
}

impl<I, T> fmt::Display for TypeError<I, T>
where
    I: fmt::Display + AsRef<str>,
    T::SpannedId: AsRef<str> + AsId<I>,
    T: TypeExt<Id = I> + ast::HasMetadata + pos::HasSpan,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let filter = self.make_filter();
        self.filter_fmt(&*filter, f)
    }
}

pub fn similarity_filter<'a, I, T>(typ: &'a T, fields: &'a [I]) -> Box<dyn Fn(&I) -> Filter + 'a>
where
    T: TypeExt<Id = I>,
    I: AsRef<str>,
    T::SpannedId: AsRef<str>,
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

impl<I, T> TypeError<I, T>
where
    I: fmt::Display + AsRef<str>,
    T::SpannedId: AsRef<str> + AsId<I>,
    T: TypeExt<Id = I> + ast::HasMetadata + pos::HasSpan,
{
    pub fn make_filter<'a>(&'a self) -> Box<dyn Fn(&I) -> Filter + 'a> {
        match *self {
            TypeError::FieldMismatch(ref l, ref r) => Box::new(move |field| {
                if [l, r].iter().any(|f| f.as_ref() == field.as_ref()) {
                    Filter::Retain
                } else {
                    Filter::Drop
                }
            }),
            TypeError::UndefinedType(_)
            | TypeError::SelfRecursiveAlias(_)
            | TypeError::UnableToGeneralize(_)
            | TypeError::EscapingSkolem(_) => Box::new(|_| Filter::Retain),
            TypeError::MissingFields(ref typ, ref fields) => similarity_filter(typ, fields),
        }
    }

    pub fn filter_fmt(&self, filter: &dyn Fn(&I) -> Filter, f: &mut fmt::Formatter) -> fmt::Result {
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
            TypeError::EscapingSkolem(ref skolem) => {
                write!(f, "Skolem variable `{}` has escaped its scope", skolem)
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

impl Substitutable for RcType<Symbol> {
    type Variable = TypeVariable;

    type Factory = ArcKind;

    type Interner = SharedInterner<Symbol, Self>;

    fn from_variable(mut subs: &Substitution<Self>, var: TypeVariable) -> Self {
        subs.variable(var)
    }

    fn into_variable(&mut self, x: Self::Variable) {
        Self::set(self, Type::Variable(x))
    }

    fn is_unique(self_: &Self) -> bool {
        RcType::strong_count(self_) == 1
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
        match &**self {
            Type::Function(ArgType::Constructor, arg, ret) => match &**ret {
                Type::Function(ArgType::Constructor, ..) => {
                    f.walk(arg);
                    f.walk(arg);
                }
                _ => f.walk(arg),
            },
            _ => types::walk_type_(self, f),
        }
    }

    fn instantiate(&self, mut subs: &Substitution<Self>) -> Self {
        self.instantiate_generics(&mut subs, &mut FnvMap::default())
    }

    fn contains_variables(&self) -> bool {
        self.flags().contains(Flags::HAS_VARIABLES)
    }
}

impl<'a> Unifiable<State<'a>> for RcType {
    type Error = TypeError<Symbol, RcType>;

    fn zip_match<U>(
        &self,
        other: &Self,
        unifier: &mut UnifierState<'a, U>,
    ) -> Result<Option<Self>, Error<Symbol, RcType>>
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
                let is_polymorphic_row = |typ: &RcType| -> bool {
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
        (&*state.subs).error()
    }
}

fn do_zip_match<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    expected: &RcType,
    actual: &RcType,
) -> Result<Option<RcType>, Error<Symbol>>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
{
    debug!("Unifying:\n{} <=> {}", expected, actual);
    let mut subs = unifier.state.subs;
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
                subs.function_type(l_arg_type, Some(arg), ret)
            }))
        }

        (
            &Type::Function(ArgType::Explicit, ref l_arg, ref l_ret),
            &Type::App(ref r, ref r_args),
        ) => {
            let l_args = collect![l_arg.clone(), l_ret.clone()];
            unify_app(unifier, &subs.function_builtin(), &l_args, r, r_args)
                .map_err(|_| UnifyError::TypeMismatch(expected.clone(), actual.clone()))
        }

        (
            &Type::App(ref l, ref l_args),
            &Type::Function(ArgType::Explicit, ref r_arg, ref r_ret),
        ) => {
            let r_args = collect![r_arg.clone(), r_ret.clone()];
            unify_app(unifier, l, l_args, &subs.function_builtin(), &r_args)
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
                .map(|row| subs.intern(Type::Variant(row)));
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
                .map(|row| subs.intern(Type::Record(row)));
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
                .map(|row| subs.intern(Type::Effect(row)));
            unifier.state.record_context = previous;
            Ok(result)
        }

        (
            &Type::ExtendRow {
                fields: ref l_args,
                rest: ref l_rest,
            },
            &Type::ExtendRow {
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
                    |fields, rest| subs.extend_row(fields, rest),
                ))
            } else if **l_rest == Type::EmptyRow && **r_rest == Type::EmptyRow {
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
                    |fields, rest| subs.extend_row(fields, rest),
                ))
            } else {
                unify_rows(unifier, expected, actual)
            }
        }

        (
            &Type::ExtendTypeRow {
                types: ref l_types,
                rest: ref l_rest,
            },
            &Type::ExtendTypeRow {
                types: ref r_types,
                rest: ref r_rest,
            },
        ) => {
            let rest_opt = unifier.try_match(l_rest, r_rest);
            if l_types == r_types {
                Ok(rest_opt.map(|rest| subs.extend_type_row(l_types.clone(), rest)))
            } else {
                return Err(UnifyError::TypeMismatch(expected.clone(), actual.clone()));
            }
        }

        (&Type::ExtendTypeRow { .. }, &Type::ExtendRow { .. })
        | (&Type::ExtendRow { .. }, &Type::ExtendTypeRow { .. })
        | (&Type::EmptyRow, &Type::ExtendTypeRow { .. })
        | (&Type::ExtendTypeRow { .. }, &Type::EmptyRow)
        | (&Type::ExtendRow { .. }, &Type::EmptyRow)
        | (&Type::EmptyRow, &Type::ExtendRow { .. }) => unify_rows(unifier, expected, actual),

        (&Type::Ident(ref id), &Type::Alias(ref alias)) if id.name == alias.name => {
            Ok(Some(actual.clone()))
        }

        (&Type::Alias(ref alias), &Type::Ident(ref id)) if id.name == alias.name => Ok(None),

        (&Type::Forall(ref params, _), &Type::Forall(_, _)) => {
            let mut named_variables = FnvMap::default();

            if unifier.state.in_alias {
                let l = expected.skolemize(&mut subs, &mut named_variables);
                named_variables.clear();
                let r = actual.skolemize(&mut subs, &mut named_variables);

                Ok(unifier
                    .try_match_res(&l, &r)?
                    .map(|inner_type| unifier.state.subs.forall(params.clone(), inner_type)))
            } else {
                let mut expected_iter = expected.forall_scope_iter();

                let mut ids = SmallVec::<[_; 5]>::new();
                named_variables.extend(expected_iter.by_ref().map(|l_param| {
                    let skolem = subs.new_skolem(l_param.id.clone(), l_param.kind.clone());
                    ids.push(skolem.get_id().expect("Skolem"));
                    (l_param.id.clone(), skolem)
                }));
                let l = expected_iter.typ.skolemize(&mut subs, &mut named_variables);

                named_variables.clear();
                let mut actual_iter = actual.forall_scope_iter();
                named_variables.extend(ids.iter().zip(actual_iter.by_ref()).map(
                    |(&id, r_param)| {
                        (
                            r_param.id.clone(),
                            subs.skolem(Skolem {
                                name: r_param.id.clone(),
                                id,
                                kind: r_param.kind.clone(),
                            }),
                        )
                    },
                ));
                let r = actual_iter.typ.skolemize(&mut subs, &mut named_variables);

                Ok(unifier
                    .try_match_res(&l, &r)?
                    .map(|inner_type| unifier.state.subs.forall(params.clone(), inner_type)))
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
                    debug!("Unify error: {} <=> {}", expected, actual);
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
    l: &RcType,
    l_args: &AppVec<RcType>,
    r: &RcType,
    r_args: &AppVec<RcType>,
) -> Result<Option<RcType>, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
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
    let mut subs = unifier.state.subs;
    match l_args.len().cmp(&r_args.len()) {
        Equal => {
            let new_type = unifier.try_match(l, r);
            let new_args =
                merge::merge_tuple_iter(l_args.iter().zip(r_args), |l, r| unifier.try_match(l, r));
            Ok(merge::merge(l, new_type, l_args, new_args, |f, a| {
                subs.app(f, a)
            }))
        }
        Less => {
            let offset = r_args.len() - l_args.len();

            let reduced_r = subs.app(r.clone(), r_args[..offset].iter().cloned().collect());
            let new_type = match unifier.try_match_res(l, &reduced_r) {
                Ok(new_type) => new_type,
                Err(_err) => {
                    return Err(());
                }
            };

            let new_args = merge::merge_tuple_iter(l_args.iter().zip(&r_args[offset..]), |l, r| {
                unifier.try_match(l, r)
            });
            Ok(merge::merge(l, new_type, l_args, new_args, |f, a| {
                subs.app(f, a)
            }))
        }
        Greater => {
            let offset = l_args.len() - r_args.len();

            let reduced_l = subs.app(l.clone(), l_args[..offset].iter().cloned().collect());
            let new_type = match unifier.try_match_res(&reduced_l, r) {
                Ok(new_type) => new_type,
                Err(_err) => {
                    return Err(());
                }
            };

            let new_args = merge::merge_tuple_iter(l_args[offset..].iter().zip(r_args), |l, r| {
                unifier.try_match(l, r)
            });
            Ok(merge::merge(r, new_type, r_args, new_args, |f, a| {
                subs.app(f, a)
            }))
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
    l: &RcType,
    r: &RcType,
) -> Result<Option<RcType>, Error<Symbol>>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
{
    let mut subs = unifier.state.subs;
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
                let l_rest = subs.extend_full_row(
                    types_missing_from_right,
                    missing_from_right,
                    rest.clone(),
                );
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
                    subs.extend_full_row(types_missing_from_left, missing_from_left, rest.clone());
                unifier.try_match(l_iter.current_type(), &r_rest);
                types.extend(r_rest.type_field_iter().cloned());
                fields.extend(r_rest.row_iter().cloned());
            }
        }
    }

    Ok(Some(subs.extend_full_row(types, fields, rest)))
}

fn resolve_application<'t>(typ: &'t RcType, mut subs: &'t Substitution<RcType>) -> Option<RcType> {
    match **typ {
        Type::App(ref f, ref a) => resolve_application(f, subs).map(|f| subs.app(f, a.clone())),
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
    Root(RcType),
    Found(RcType),
    AlreadyDone,
}

/// Attempt to unify two alias types.
/// To find a possible successful unification we walk through the alias expansions of `l` in an
/// attempt to find that `l` expands to the alias `r_id`
fn find_alias<'a, U>(
    unifier: &mut UnifierState<'a, U>,
    l: RcType,
    r_id: &SymbolRef,
) -> Result<FoundAlias, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
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
    mut l: RcType,
    r_id: &SymbolRef,
) -> Result<FoundAlias, ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
{
    let mut did_alias = false;
    let mut subs = unifier.state.subs;
    loop {
        l = match l.name() {
            Some(l_id) => {
                if let Some(l_id) = l.alias_ident() {
                    if unifier.state.reduced_aliases.iter().any(|id| id == l_id) {
                        return Err(());
                    }
                }
                if l_id == r_id {
                    // If the aliases matched before going through an alias there is no need to
                    // return a replacement type
                    return Ok(if did_alias {
                        FoundAlias::Found(l.clone())
                    } else {
                        FoundAlias::AlreadyDone
                    });
                }
                match resolve::remove_alias(unifier.state.env, &mut subs, &l) {
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
    expected: &RcType,
    actual: &RcType,
    through_alias: &mut bool,
) -> Result<(RcType, RcType), ()>
where
    UnifierState<'a, U>: Unifier<State<'a>, RcType>,
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

/// Performs subsumption between `l` and `r` (`r` is-a `l`)
pub fn subsumes(
    subs: &Substitution<RcType>,
    state: State,
    l: &RcType,
    r: &RcType,
) -> Result<RcType, (RcType, Errors<Error<Symbol>>)> {
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

pub fn subsumes_implicit(
    subs: &Substitution<RcType>,
    state: State,
    l: &RcType,
    r: &RcType,
    receiver: &mut dyn FnMut(&RcType),
) -> Result<RcType, (RcType, Errors<Error<Symbol>>)> {
    debug!("Subsume {} <=> {}", l, r);
    let mut unifier = UnifierState {
        state: state,
        unifier: Subsume {
            subs: subs,
            errors: Errors::new(),
            allow_returned_type_replacement: true,
        },
    };

    let typ = unifier.subsumes_implicit(l, r, receiver);
    if unifier.unifier.errors.has_errors() {
        Err((typ.unwrap_or_else(|| l.clone()), unifier.unifier.errors))
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

pub fn subsumes_no_subst(
    state: State,
    l: &RcType,
    r: &RcType,
) -> Result<RcType, (RcType, Errors<Error<Symbol>>)> {
    debug!("Subsume {} <=> {}", l, r);
    let mut unifier = UnifierState {
        unifier: Subsume {
            subs: state.subs,
            errors: Errors::new(),
            allow_returned_type_replacement: true,
        },
        state: state,
    };

    let typ = unifier.try_match(l, r);
    if unifier.unifier.errors.has_errors() {
        Err((typ.unwrap_or_else(|| l.clone()), unifier.unifier.errors))
    } else {
        Ok(typ.unwrap_or_else(|| l.clone()))
    }
}

struct Subsume<'e> {
    subs: &'e Substitution<RcType>,
    errors: Errors<Error<Symbol>>,
    allow_returned_type_replacement: bool,
}

impl<'a, 'e> UnifierState<'a, Subsume<'e>> {
    fn subsumes_implicit(
        &mut self,
        l: &RcType,
        r: &RcType,
        receiver: &mut dyn FnMut(&RcType),
    ) -> Option<RcType> {
        debug!("Subsume implicit {} <=> {}", l, r);

        // Act as the implicit arguments of `actual` has been supplied (unless `expected` is
        // specified to have implicit arguments)

        let l_orig = &l;
        let mut map = FnvMap::default();

        let r = r.instantiate_generics(&mut self.unifier.subs, &mut FnvMap::default());
        let typ = match *r {
            Type::Function(ArgType::Implicit, ref arg_type, ref r_ret) => {
                let l = l.skolemize(&mut self.unifier.subs, &mut map);

                match **self.unifier.subs.real(&l) {
                    Type::Function(ArgType::Implicit, _, _) => self.subsume_check(&l, &r),

                    _ => {
                        receiver(&arg_type);

                        self.subsumes_implicit(&l, r_ret, receiver);
                        None
                    }
                }
            }
            _ => self.try_match(&l, &r),
        };

        // If a skolem variable we just created somehow appears in the original type it has been
        // unified with a type variable outside of this skolem scope meaning it has escaped
        //
        // Unifying:
        // forall s . Test s 2 <=> Test 1 1
        //      ^ skolemize
        // ==> 1 <=> s@3
        // ==> 1 <=> 2
        // ==> s@3 <=> 2
        //
        // `l_orig` is still `forall s . Test s 2` so we can detect `s@2` escaping in the
        // variable `2`
        if !map.is_empty() {
            self.skolem_escape_check(&map, l_orig);
        }

        typ.or(if l_orig.forall_params().next().is_some() {
            Some(l.clone())
        } else {
            None
        })
        .map(|typ| {
            self.unifier.allow_returned_type_replacement = false;
            self.unifier.subs.with_forall(typ, l_orig)
        })
    }

    fn subsume_check(&mut self, l: &RcType, r: &RcType) -> Option<RcType> {
        let l_orig = &l;
        let mut map = FnvMap::default();
        let l = l.skolemize(&mut self.unifier.subs, &mut map);
        let typ = self.try_match(&l, r);

        // If a skolem variable we just created somehow appears in the original type it has been
        // unified with a type variable outside of this skolem scope meaning it has escaped
        //
        // Unifying:
        // forall s . Test s 2 <=> Test 1 1
        //      ^ skolemize
        // ==> 1 <=> s@3
        // ==> 1 <=> 2
        // ==> s@3 <=> 2
        //
        // `l_orig` is still `forall s . Test s 2` so we can detect `s@2` escaping in the
        // variable `2`
        self.skolem_escape_check(&map, l_orig);

        typ.or(if l_orig.forall_params().next().is_some() {
            Some(l.clone())
        } else {
            None
        })
        .map(|typ| {
            self.unifier.allow_returned_type_replacement = false;
            self.unifier.subs.with_forall(typ, l_orig)
        })
    }

    fn skolem_escape_check(&mut self, skolem_scope: &FnvMap<Symbol, RcType>, typ: &RcType) {
        let typ = self.unifier.subs.real(typ);
        match **typ {
            Type::Skolem(ref skolem) => match skolem_scope.get(&skolem.name).map(|t| &**t) {
                Some(Type::Skolem(other)) if other.id == skolem.id => self.report_error(
                    UnifyError::Other(TypeError::EscapingSkolem(skolem.name.clone())),
                ),
                _ => (),
            },
            _ => types::walk_type_(
                typ,
                &mut types::ControlVisitation(|typ: &RcType| {
                    self.skolem_escape_check(skolem_scope, typ)
                }),
            ),
        }
    }

    fn subsume_check_rho(&mut self, l: &RcType, r: &RcType) -> Option<RcType> {
        self.try_match(l, r)
    }

    fn subsume_check_function(
        &mut self,
        arg_l: &RcType,
        ret_l: &RcType,
        arg_r: &RcType,
        ret_r: &RcType,
    ) -> Option<RcType> {
        let mut subs = self.state.subs;
        let arg = self.subsume_check(arg_r, arg_l);
        let ret = self.subsume_check_rho(ret_l, ret_r);
        merge::merge(arg_l, arg, ret_l, ret, |arg, ret| {
            subs.function(vec![arg], ret)
        })
    }

    fn unify_function(&mut self, actual: &RcType) -> (RcType, RcType) {
        self.remove_aliases_in(actual, |self_, actual| {
            let subs = self_.state.subs;

            match actual.as_explicit_function() {
                Some((arg, ret)) => return (arg.clone(), ret.clone()),
                None => (),
            }

            let arg = subs.new_var();
            let ret = subs.new_var();
            let f = self_.state.subs.function(Some(arg.clone()), ret.clone());
            if let Err(errors) = unify::unify(subs, self_.state.clone(), &f, &actual) {
                for err in errors {
                    self_.report_error(err);
                }
            }

            (arg, ret)
        })
    }

    fn remove_aliases_in<R>(&mut self, typ: &RcType, f: impl FnOnce(&mut Self, &RcType) -> R) -> R {
        let subs = self.state.subs;

        let before = self.state.reduced_aliases.len();

        let typ = match self.state.remove_aliases(subs, &typ) {
            Ok(t) => t.map_or_else(|| Cow::Borrowed(typ), Cow::Owned),
            Err(err) => {
                self.report_error(UnifyError::Other(err));
                Cow::Borrowed(typ)
            }
        };

        let r = f(self, &typ);

        self.state.reduced_aliases.truncate(before);

        r
    }
}

impl<'a, 'e> Unifier<State<'a>, RcType> for UnifierState<'a, Subsume<'e>> {
    fn report_error(&mut self, error: UnifyError<TypeError<Symbol, RcType>, RcType>) {
        debug!("Error {}", error);
        self.unifier.errors.push(error);
    }

    fn allow_returned_type_replacement(&self) -> bool {
        self.unifier.allow_returned_type_replacement
    }

    fn try_match_res(
        &mut self,
        l: &RcType,
        r: &RcType,
    ) -> Result<Option<RcType>, UnifyError<TypeError<Symbol, RcType>, RcType>> {
        let mut subs = self.unifier.subs;
        let l = subs.real(l);
        let r = subs.real(r);
        debug!("{} <=> {}", l, r);
        // `l` and `r` must have the same type, if one is a variable that variable is
        // unified with whatever the other type is
        match (&**l, &**r) {
            (Type::Hole, _) => Ok(Some(r.clone())),

            (_, Type::Variable(_)) => {
                debug!("Union merge {} <> {}", l, r);
                subs.union(r, l)?;
                Ok(None)
            }
            (Type::Variable(_), _) => {
                debug!("Union merge {} <> {}", l, r);
                subs.union(l, r)?;
                Ok(Some(r.clone()))
            }

            (Type::Skolem(l_skolem), _) if self.state.refinement => {
                debug!("Skolem union {} <> {}", l, r);
                match &**r {
                    Type::Skolem(r_skolem) if r_skolem.id > l_skolem.id => subs.union(r, l)?,
                    _ => subs.union(l, r)?,
                }
                Ok(None)
            }

            (_, Type::Skolem(_)) if self.state.refinement => {
                debug!("Skolem union {} <> {}", l, r);
                subs.union(r, l)?;
                Ok(None)
            }

            (_, Type::Forall(params, r)) => {
                let mut variables = params
                    .iter()
                    .map(|param| (param.id.clone(), subs.new_var()))
                    .collect();
                let r = r.instantiate_generics(&mut subs, &mut variables);
                self.try_match_res(l, &r)
            }

            (Type::Forall(_, _), _) => Ok(self.subsume_check(l, r)),

            _ => {
                // Both sides are concrete types, the only way they can be equal is if
                // the matcher finds their top level to be equal (and their sub-terms
                // unify)
                match (l.as_explicit_function(), r.as_explicit_function()) {
                    (None, None) => l.zip_match(r, self),
                    (l_func, r_func) => {
                        let x;
                        let (arg_l, ret_l) = match l_func {
                            Some(x) => x,
                            None => {
                                x = self.unify_function(l);
                                (&x.0, &x.1)
                            }
                        };
                        let y;
                        let (arg_r, ret_r) = match r_func {
                            Some(y) => y,
                            None => {
                                y = self.unify_function(r);
                                (&y.0, &y.1)
                            }
                        };
                        Ok(self.subsume_check_function(arg_l, ret_l, &arg_r, &ret_r))
                    }
                }
            }
        }
    }

    fn error_type(&self) -> RcType {
        RcType::error_type(&self.state)
    }
}

pub fn equal(state: State, l: &RcType, r: &RcType) -> bool {
    trace!("Equal {} <=> {}", l, r);
    let mut unifier = UnifierState {
        unifier: Equal {
            subs: state.subs,
            equal: true,
        },
        state,
    };

    unifier.try_match(l, r);
    unifier.unifier.equal
}

struct Equal<'e> {
    subs: &'e Substitution<RcType>,
    equal: bool,
}

impl<'a, 'e> Unifier<State<'a>, RcType> for UnifierState<'a, Equal<'e>> {
    fn report_error(&mut self, error: UnifyError<TypeError<Symbol, RcType>, RcType>) {
        debug!("Equal: Error {}", error);
        self.unifier.equal = false;
    }

    fn try_match_res(
        &mut self,
        l: &RcType,
        r: &RcType,
    ) -> Result<Option<RcType>, UnifyError<TypeError<Symbol, RcType>, RcType>> {
        let subs = self.unifier.subs;
        let l = subs.real(l);
        let r = subs.real(r);
        debug!("{} <=> {}", l, r);
        l.zip_match(r, self)
    }

    fn error_type(&self) -> RcType {
        RcType::error_type(&self.state)
    }
}

pub fn smaller(state: State, new_type: &RcType, old_type: &RcType) -> Size {
    trace!("smaller: {} < {}", new_type, old_type);
    let mut unifier = UnifierState {
        unifier: Smaller {
            size: Size::Equal,
            just_encountered_error: false,
        },
        state,
    };

    unifier.try_match(new_type, old_type);
    let size = unifier.unifier.size;
    trace!("smaller return: {:?}", size);
    size
}

#[derive(PartialEq, Debug)]
pub enum Size {
    Smaller,
    Equal,
    Different,
}

struct Smaller {
    size: Size,
    just_encountered_error: bool,
}

impl<'a, 'e> Unifier<State<'a>, RcType> for UnifierState<'a, Smaller> {
    fn report_error(&mut self, error: UnifyError<TypeError<Symbol, RcType>, RcType>) {
        debug!("Smaller: Error {}", error);
    }

    fn try_match_res(
        &mut self,
        l: &RcType,
        r: &RcType,
    ) -> Result<Option<RcType>, UnifyError<TypeError<Symbol, RcType>, RcType>> {
        if self.unifier.size == Size::Different {
            return Ok(None);
        }
        trace!("{} <=> {}", l, r);

        match (&**l, &**r) {
            // zip_match substitutes variables so we need to intercept variables here and compare
            // them manually
            (Type::Variable(_), _) | (_, Type::Variable(_)) => {
                if l != r {
                    self.unifier.size = Size::Different;
                }
                Ok(None)
            }

            _ => match l.zip_match(r, self) {
                Err(_) => {
                    self.unifier.size = Size::Different;
                    walk_type(r, &mut |inner_type: &RcType| {
                        if inner_type == l {
                            self.unifier.size = Size::Smaller
                        }
                    });
                    if self.unifier.size == Size::Different {
                        self.unifier.just_encountered_error = true;
                    }
                    Ok(None)
                }
                result => {
                    if self.unifier.just_encountered_error {
                        self.unifier.just_encountered_error = false;
                        // We ended up finding a mismatch inside this type so we need to try the check
                        // again in case the only cause for the error is that we resolved an alias
                        // which then mismatched
                        walk_type(r, &mut |inner_type: &RcType| {
                            if inner_type == l {
                                self.unifier.size = Size::Smaller
                            }
                        });
                    }
                    result
                }
            },
        }
    }

    fn error_type(&self) -> RcType {
        RcType::error_type(&self.state)
    }
}

pub fn instantiation<'a>(
    env: &'a (dyn TypeEnv<Type = RcType> + 'a),
    f: &mut dyn FnMut(&Symbol, &RcType),
    l: &RcType,
    r: &RcType,
) {
    let subs = Default::default();
    let state = State::new(env, &subs);
    let mut unifier = UnifierState {
        unifier: Instantiation { consumer: f },
        state,
    };

    unifier.try_match(l, r);
}

pub struct Instantiation<'a, 'b> {
    consumer: &'a mut (dyn FnMut(&Symbol, &RcType) + 'b),
}

impl<'a> Unifier<State<'a>, RcType> for UnifierState<'a, Instantiation<'_, '_>> {
    fn report_error(&mut self, _error: UnifyError<TypeError<Symbol, RcType>, RcType>) {}

    fn try_match_res(
        &mut self,
        l: &RcType,
        r: &RcType,
    ) -> Result<Option<RcType>, UnifyError<TypeError<Symbol, RcType>, RcType>> {
        match (&**l, &**r) {
            (Type::Generic(l), _) => {
                (self.unifier.consumer)(&l.id, r);
                Ok(None)
            }

            _ => l.zip_match(r, self),
        }
    }

    fn error_type(&self) -> RcType {
        RcType::error_type(&self.state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::error::Errors;

    use crate::base::kind::Kind;
    use crate::base::types::{Field, SharedInterner};
    use crate::substitution::Substitution;
    use crate::tests::*;
    use crate::unify::unify;
    use crate::unify::Error::*;

    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::try_init();
        let (x, y) = (intern("x"), intern("y"));
        let interner = SharedInterner::default();
        let l: RcType = interner.record(
            vec![],
            vec![
                Field::new(x.clone(), (&interner).int()),
                Field::new(y.clone(), (&interner).string()),
            ],
        );
        let r = interner.record(
            vec![],
            vec![
                Field::new(x.clone(), (&interner).string()),
                Field::new(y.clone(), (&interner).int()),
            ],
        );
        let env = MockEnv;
        let subs = Substitution::new(Kind::typ(), interner.clone());
        let state = State::new(&env, &subs);
        let result = unify(&subs, state, &l, &r);
        assert_eq!(
            result,
            Err(Errors::from(vec![
                TypeMismatch(interner.int(), interner.string()),
                TypeMismatch(interner.string(), interner.int()),
            ]))
        );
    }

    #[test]
    fn unify_row_polymorphism() {
        let _ = ::env_logger::try_init();

        let env = MockEnv;
        let mut interner = SharedInterner::default();
        let subs = Substitution::new(Kind::typ(), interner.clone());
        let state = State::new(&env, &subs);

        let x = Field::new(intern("x"), interner.int());
        let y = Field::new(intern("y"), interner.int());
        let l: RcType = interner.poly_record(vec![], vec![x.clone()], subs.new_var());
        let r = interner.poly_record(vec![], vec![y.clone()], subs.new_var());

        match unify(&subs, state, &l, &r) {
            Ok(result) => {
                // Get the row variable at the end of the resulting type so we can compare the types
                let mut iter = result.row_iter();
                for _ in iter.by_ref() {}
                let row_variable = iter.current_type().clone();
                let expected =
                    interner.poly_record(vec![], vec![x.clone(), y.clone()], row_variable);
                assert_eq!(result, expected);
            }
            Err(err) => ice!("{}", err),
        }
    }
}
