use std::{cell::RefCell, convert::TryInto, fmt, rc::Rc, sync::Arc};

use {itertools::Itertools, smallvec::SmallVec};

use rpds;

use codespan_reporting::{Diagnostic, Label};

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent},
    error::AsDiagnostic,
    fnv::FnvMap,
    metadata::Metadata,
    pos::{self, BytePos, Span, Spanned},
    resolve,
    scoped_map::{self, ScopedMap},
    symbol::Symbol,
    types::{self, ArgType, BuiltinType, Flags, Generic, SymbolKey, Type, TypeContext, TypeExt},
};

use crate::{
    substitution::Substitution,
    typ::RcType,
    typecheck::{TypeError, Typecheck},
    unify_type::{self, Size},
    TypecheckEnv,
};

fn split_type<'a>(
    subs: &'a Substitution<RcType>,
    typ: &'a RcType,
) -> Option<(SymbolKey, Option<&'a RcType>)> {
    let symbol = match **subs.real(typ) {
        Type::App(ref id, ref args) => {
            return split_type(subs, id)
                .map(|(k, _)| k)
                .map(|key| (key, if args.len() == 1 { args.get(0) } else { None }));
        }
        Type::Function(ArgType::Implicit, _, ref ret_type) => {
            split_type(subs, ret_type)
                    // Usually the implicit argument will appear directly inside type whose `SymbolKey`
                    // that was returned so it is unlikely that partitition further
                    .map(|(s, _)| s)
        }
        Type::Function(ArgType::Explicit, ..) => {
            Some(SymbolKey::Ref(BuiltinType::Function.symbol()))
        }
        Type::Skolem(ref skolem) => Some(SymbolKey::Owned(skolem.name.clone())),
        Type::Ident(ref id) => Some(SymbolKey::Owned(id.clone())),
        Type::Alias(ref alias) => Some(SymbolKey::Owned(alias.name.clone())),
        Type::Builtin(ref builtin) => Some(SymbolKey::Ref(builtin.symbol())),
        Type::Forall(_, ref typ) => return split_type(subs, typ),
        _ => None,
    };
    symbol.map(|s| (s, None))
}

type ImplicitBinding = (Rc<[TypedIdent<Symbol, RcType>]>, RcType);

pub struct Partition<T> {
    partition: FnvMap<SymbolKey, Partition<T>>,
    // The partitioning should be very fine grained so we usually have very few elements in each
    // partition
    rest: SmallVec<[(Level, T); 3]>,
}

impl<T> fmt::Debug for Partition<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Partition")
            .field(
                "partition",
                &format_args!(
                    "[{}]",
                    self.partition
                        .iter()
                        .format_with(",", |(_, i), f| f(&format_args!("{:?}", i)))
                ),
            )
            .field(
                "rest",
                &format_args!(
                    "[{}]",
                    self.rest
                        .iter()
                        .format_with(",", |(_, i), f| f(&format_args!("{:?}", i)))
                ),
            )
            .finish()
    }
}

impl fmt::Display for Partition<ImplicitBinding> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Partition")
            .field(
                "partition",
                &format_args!(
                    "[{}]",
                    self.partition
                        .iter()
                        .format_with(",", |i, f| f(&format_args!("{}", i.1)))
                ),
            )
            .field(
                "rest",
                &format_args!(
                    "[{}]",
                    self.rest.iter().format_with(",", |i, f| f(&format_args!(
                        "@{:?} {}: {}",
                        i.0,
                        (i.1).0.iter().map(|i| &i.name).format("."),
                        (i.1).1
                    )))
                ),
            )
            .finish()
    }
}

impl<T> Default for Partition<T> {
    fn default() -> Self {
        Partition {
            partition: Default::default(),
            rest: Default::default(),
        }
    }
}

impl<T> Partition<T> {
    fn insert(&mut self, subs: &Substitution<RcType>, typ: Option<&RcType>, level: Level, value: T)
    where
        T: Clone,
    {
        self.insert_(subs, typ, level, value);
        // Ignore the insertion request at the top level as we know that the partitioning is 100%
        // correct here (it matches on the implicit type rather than the argument to the implicit
        // type)
    }

    fn insert_(
        &mut self,
        subs: &Substitution<RcType>,
        typ: Option<&RcType>,
        level: Level,
        value: T,
    ) -> bool
    where
        T: Clone,
    {
        match typ.and_then(|typ| split_type(subs, typ)) {
            Some((symbol, rest)) => {
                let partition = self.partition.entry(symbol).or_default();
                if partition.insert_(subs, rest, level, value.clone()) {
                    // Add a fallback value, ideally we shouldn't need this
                    partition.rest.push((level, value));
                }
                true
            }
            None => {
                self.rest.push((level, value));
                false
            }
        }
    }

    fn remove(&mut self, subs: &Substitution<RcType>, typ: Option<&RcType>) -> bool {
        match typ.and_then(|typ| split_type(subs, typ)) {
            Some((symbol, rest)) => {
                let partition = self
                    .partition
                    .get_mut(&symbol)
                    .expect("Entry from insert call");
                if partition.remove(subs, rest) {
                    partition.rest.pop();
                }
                true
            }
            None => {
                self.rest.pop();
                false
            }
        }
    }

    fn get_candidates<'a>(
        &'a self,
        subs: &Substitution<RcType>,
        typ: Option<&RcType>,
        implicit_bindings_level: Level,
        consumer: &mut impl FnMut(&'a T),
    ) -> Option<()>
    where
        T: fmt::Debug,
    {
        fn f<U>(t: &(Level, U)) -> &U {
            &t.1
        }
        match typ.and_then(|typ| split_type(subs, &typ)) {
            Some((symbol, rest)) => {
                match self.partition.get(&symbol).and_then(|bindings| {
                    bindings.get_candidates(subs, rest, implicit_bindings_level, consumer)
                }) {
                    Some(()) => Some(()),
                    None => {
                        let end = self
                            .rest
                            .iter()
                            .rposition(|(level, _)| *level <= implicit_bindings_level)
                            .map_or(0, |i| i + 1);
                        self.rest[..end].iter().map(f).for_each(consumer);
                        if end == 0 {
                            None
                        } else {
                            Some(())
                        }
                    }
                }
            }
            None => {
                let end = self
                    .rest
                    .iter()
                    .rposition(|(level, _)| *level <= implicit_bindings_level)
                    .map_or(0, |i| i + 1);
                self.rest[..end].iter().map(f).for_each(consumer);
                if end == 0 {
                    None
                } else {
                    Some(())
                }
            }
        }
    }
}

impl Partition<ImplicitBinding> {
    fn update<F>(&mut self, f: &mut F)
    where
        F: FnMut(&Symbol) -> Option<RcType>,
    {
        for partition in self.partition.values_mut() {
            partition.update(f);
        }

        for (_, (path, typ)) in &mut self.rest {
            if path.len() == 1 {
                let name = &path[0].name;
                if let Some(t) = f(name) {
                    *typ = t;
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Level(u32);

#[derive(Default, Debug)]
pub(crate) struct ImplicitBindings {
    pub partition: Partition<ImplicitBinding>,
    partition_insertions: Vec<Option<(RcType, Option<Symbol>)>>,
    pub definitions: ScopedMap<Symbol, ()>,
}

impl fmt::Display for ImplicitBindings {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.partition)
    }
}

impl ImplicitBindings {
    fn insert(
        &mut self,
        subs: &Substitution<RcType>,
        definition: Option<&Symbol>,
        path: &[TypedIdent<Symbol, RcType>],
        typ: &RcType,
    ) {
        if let Some(definition) = definition {
            self.definitions.insert(definition.clone(), ());
        }

        let level = Level(self.partition_insertions.len().try_into().unwrap());

        self.partition
            .insert(subs, Some(typ), level, (Rc::from(&path[..]), typ.clone()));

        self.partition_insertions
            .push(Some((typ.clone(), definition.cloned())));
    }

    pub fn update<F>(&mut self, mut f: F)
    where
        F: FnMut(&Symbol) -> Option<RcType>,
    {
        self.partition.update(&mut f);
    }

    fn get_candidates<'a>(
        &'a self,
        subs: &Substitution<RcType>,
        typ: &RcType,
        level: Level,
    ) -> impl DoubleEndedIterator<Item = ImplicitBinding> {
        let mut candidates = Vec::new();
        self.partition
            .get_candidates(subs, Some(typ), level, &mut |bind| {
                candidates.push(bind.clone())
            });
        candidates.into_iter()
    }

    pub fn enter_scope(&mut self) {
        self.definitions.enter_scope();
        self.partition_insertions.push(None);
    }

    pub fn exit_scope(&mut self, subs: &Substitution<RcType>) {
        self.definitions.exit_scope();
        while let Some(Some((typ, definition))) = self.partition_insertions.pop() {
            if let Some(definition) = definition {
                self.definitions.remove(&definition);
            }
            self.partition.remove(subs, Some(&typ));
        }
    }
}

type Result<T> = ::std::result::Result<T, Error<RcType>>;

#[derive(Debug, PartialEq, Functor)]
pub struct Error<T> {
    pub kind: ErrorKind<T>,
    pub reason: rpds::List<T>,
}

impl<I: fmt::Display + Clone> fmt::Display for Error<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl<I: fmt::Display + Clone> AsDiagnostic for Error<I> {
    fn as_diagnostic(&self) -> Diagnostic {
        let diagnostic = Diagnostic::new_error(self.to_string());
        self.reason.iter().fold(diagnostic, |diagnostic, reason| {
            diagnostic.with_label(
                Label::new_secondary(Span::new(BytePos::none(), BytePos::none())).with_message(
                    format!("Required because of an implicit parameter of `{}`", reason),
                ),
            )
        })
    }
}

#[derive(Debug, PartialEq, Functor)]
pub struct AmbiguityEntry<T> {
    pub path: String,
    pub typ: T,
}

#[derive(Debug, PartialEq, Functor)]
pub enum ErrorKind<T> {
    /// An implicit parameter were not possible to resolve
    MissingImplicit(T),
    LoopInImplicitResolution(Vec<String>),
    AmbiguousImplicit(Vec<AmbiguityEntry<T>>),
}

impl<I: fmt::Display> fmt::Display for ErrorKind<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ErrorKind::*;
        match *self {
            MissingImplicit(ref typ) => write!(
                f,
                "Implicit parameter with type `{}` could not be resolved.",
                typ,
            ),
            LoopInImplicitResolution(ref paths) => write!(
                f,
                "Unable to resolve implicit, possible infinite loop. When resolving, {}",
                paths.iter().format(", ")
            ),
            AmbiguousImplicit(ref candidates) => write!(
                f,
                "Unable to resolve implicit. Multiple candidates were found: {}",
                candidates
                    .iter()
                    .format_with(", ", |entry, fmt| fmt(&format_args!(
                        "{}: {}",
                        entry.path, entry.typ
                    )))
            ),
        }
    }
}

struct Demand {
    reason: rpds::List<RcType>,
    constraint: RcType,
}

struct ResolveImplicitsVisitor<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
}

impl<'a, 'b> ResolveImplicitsVisitor<'a, 'b> {
    fn resolve_implicit(
        &mut self,
        implicit_bindings_level: Level,
        expr: &SpannedExpr<Symbol>,
        id: &TypedIdent<Symbol, RcType>,
    ) -> Option<SpannedExpr<Symbol>> {
        debug!(
            "Resolving {} against:\n{}",
            id.typ,
            self.tc
                .implicit_resolver
                .implicit_bindings
                .get_candidates(&self.tc.subs, &id.typ, implicit_bindings_level)
                .map(|t| t.1)
                .format("\n")
        );
        self.tc.implicit_resolver.visited.clear();
        let span = expr.span;
        let mut to_resolve = Vec::new();
        match self.find_implicit(
            implicit_bindings_level,
            &mut to_resolve,
            &Demand {
                reason: rpds::List::new(),
                constraint: id.typ.clone(),
            },
        ) {
            Ok(path_of_candidate) => {
                debug!(
                    "Found implicit candidate `{}`. Trying its implicit arguments (if any)",
                    path_of_candidate
                        .iter()
                        .rev()
                        .map(|id| &id.name)
                        .format(".")
                );

                let resolution_result = match self.resolve_implicit_application(
                    0,
                    implicit_bindings_level,
                    span,
                    &path_of_candidate,
                    &to_resolve,
                ) {
                    Ok(opt) => opt.map(Ok),
                    Err(err) => Some(Err(err)),
                };

                match resolution_result {
                    Some(Ok(replacement)) => Some(replacement),
                    Some(Err(err)) => {
                        debug!("UnableToResolveImplicit {:?} {}", id.name, id.typ);
                        self.tc.errors.push(Spanned {
                            span: expr.span,
                            value: TypeError::UnableToResolveImplicit(err).into(),
                        });
                        None
                    }
                    None => {
                        debug!("UnableToResolveImplicit {:?} {}", id.name, id.typ);
                        self.tc.errors.push(Spanned {
                            span: expr.span,
                            value: TypeError::UnableToResolveImplicit(Error {
                                kind: ErrorKind::MissingImplicit(id.typ.clone()),
                                reason: to_resolve
                                    .first()
                                    .map_or_else(rpds::List::new, |demand| demand.reason.clone()),
                            })
                            .into(),
                        });
                        None
                    }
                }
            }
            Err(err) => {
                debug!("UnableToResolveImplicit {:?} {}", id.name, id.typ);
                self.tc.errors.push(Spanned {
                    span: expr.span,
                    value: TypeError::UnableToResolveImplicit(err).into(),
                });
                None
            }
        }
    }

    fn resolve_implicit_application(
        &mut self,
        level: u32,
        implicit_bindings_level: Level,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<Symbol>>> {
        self.resolve_implicit_application_(level, implicit_bindings_level, span, path, to_resolve)
            .map_err(|mut err| {
                if let ErrorKind::LoopInImplicitResolution(ref mut paths) = err.kind {
                    paths.push(path.iter().map(|id| &id.name).format(".").to_string());
                }
                err
            })
    }

    fn resolve_implicit_application_(
        &mut self,
        level: u32,
        implicit_bindings_level: Level,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<Symbol>>> {
        let func = path[1..].iter().fold(
            pos::spanned(
                span,
                Expr::Ident(TypedIdent::new2(
                    path[0].name.clone(),
                    self.tc.subs.bind_arc(&path[0].typ),
                )),
            ),
            |expr, ident| {
                pos::spanned(
                    expr.span,
                    Expr::Projection(
                        Box::new(expr),
                        ident.name.clone(),
                        self.tc.subs.bind_arc(&ident.typ),
                    ),
                )
            },
        );

        Ok(if to_resolve.is_empty() {
            Some(func)
        } else {
            let resolved_arguments = to_resolve
                .iter()
                .filter_map(|demand| {
                    self.tc.implicit_resolver.visited.enter_scope();

                    let mut to_resolve = Vec::new();
                    let result = self
                        .find_implicit(implicit_bindings_level, &mut to_resolve, demand)
                        .and_then(|path| {
                            debug!("Success! Resolving arguments");
                            self.resolve_implicit_application(
                                level + 1,
                                implicit_bindings_level,
                                span,
                                &path,
                                &to_resolve,
                            )
                        });

                    self.tc.implicit_resolver.visited.exit_scope();

                    match result {
                        Ok(opt) => opt.map(Ok),
                        Err(err) => Some(Err(err)),
                    }
                })
                .collect::<Result<Vec<_>>>()?;

            if resolved_arguments.len() == to_resolve.len() {
                Some(pos::spanned(
                    span,
                    Expr::App {
                        func: Box::new(func),
                        args: resolved_arguments,
                        implicit_args: Vec::new(),
                    },
                ))
            } else {
                None
            }
        })
    }

    fn try_resolve_implicit(
        &mut self,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
        binding_type: &RcType,
    ) -> bool {
        debug!(
            "Trying implicit {{\n    path: `{}`,\n    to_resolve: [{}],\n    demand: `{}`,\n    binding_type: {} }}",
            path.iter().map(|id| &id.name).format("."),
            to_resolve.iter().map(|d| &d.constraint).format(", "),
            self.tc.subs.zonk(&demand.constraint),
            binding_type,
        );

        let binding_type = self.tc.instantiate_generics(&binding_type);
        to_resolve.clear();
        let mut iter = types::implicit_arg_iter(&binding_type);
        to_resolve.extend(iter.by_ref().cloned().map(|constraint| Demand {
            reason: demand.reason.push_front(binding_type.clone()),
            constraint,
        }));

        let state = crate::unify_type::State::new(&self.tc.environment, &self.tc.subs);
        crate::unify_type::subsumes(&self.tc.subs, state, &demand.constraint, &iter.typ).is_ok()
    }

    fn find_implicit(
        &mut self,
        implicit_bindings_level: Level,
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
    ) -> Result<Rc<[TypedIdent<Symbol, RcType>]>> {
        let mut candidates = self
            .tc
            .implicit_resolver
            .implicit_bindings
            .get_candidates(&self.tc.subs, &demand.constraint, implicit_bindings_level)
            .rev();
        let found_candidate = candidates.by_ref().find(|x| {
            let (path, typ) = &*x;
            self.try_resolve_implicit(path, to_resolve, demand, typ)
        });
        match found_candidate {
            Some(x) => {
                let (candidate_path, candidate_type) = &x;
                let new_demands = to_resolve
                    .iter()
                    .map(|d| self.tc.subs.zonk(&d.constraint))
                    .collect::<Vec<_>>()
                    .into_boxed_slice();

                match self.tc.implicit_resolver.visited.entry(
                    candidate_path
                        .iter()
                        .map(|id| id.name.clone())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                ) {
                    scoped_map::Entry::Vacant(entry) => {
                        entry.insert(new_demands);
                    }
                    scoped_map::Entry::Occupied(mut entry) => {
                        trace!(
                            "Smaller check: [{}] < [{}]",
                            new_demands.iter().format(", "),
                            entry.get().iter().format(", "),
                        );

                        let state = unify_type::State::new(&self.tc.environment, &self.tc.subs);
                        if !smallers(state, &new_demands, entry.get()) {
                            return Err(Error {
                                kind: ErrorKind::LoopInImplicitResolution(vec![candidate_path
                                    .iter()
                                    .map(|id| &id.name)
                                    .format(".")
                                    .to_string()]),
                                reason: demand.reason.clone(),
                            });
                        }
                        // Update the demands with to these new, smaller demands
                        entry.insert(new_demands);
                    }
                }

                let mut additional_candidates: Vec<_> = candidates
                    .filter(|x| {
                        let (path, typ) = &*x;
                        self.try_resolve_implicit(path, &mut Vec::new(), demand, typ)
                    })
                    .map(|bind| AmbiguityEntry {
                        path: bind.0.iter().map(|id| &id.name).format(".").to_string(),
                        typ: bind.1.clone(),
                    })
                    .collect();
                if additional_candidates.is_empty() {
                    Ok(candidate_path.clone())
                } else {
                    additional_candidates.push(AmbiguityEntry {
                        path: candidate_path
                            .iter()
                            .map(|id| &id.name)
                            .format(".")
                            .to_string(),
                        typ: candidate_type.clone(),
                    });
                    Err(Error {
                        kind: ErrorKind::AmbiguousImplicit(additional_candidates),
                        reason: demand.reason.clone(),
                    })
                }
            }
            None => Err(Error {
                kind: ErrorKind::MissingImplicit(demand.constraint.clone()),
                reason: demand.reason.clone(),
            }),
        }
    }
}

impl<'a, 'b, 'c> MutVisitor<'c> for ResolveImplicitsVisitor<'a, 'b> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
        let mut replacement = None;
        if let Expr::Ident(ref id) = expr.value {
            let implicit_bindings_level = self
                .tc
                .implicit_resolver
                .implicit_vars
                .get(&id.name)
                .cloned();
            if let Some(implicit_bindings_level) = implicit_bindings_level {
                let typ = id.typ.clone();
                let id = TypedIdent {
                    name: id.name.clone(),
                    typ: typ,
                };
                replacement = self.resolve_implicit(implicit_bindings_level, expr, &id);
            }
        }
        if let Some(replacement) = replacement {
            *expr = replacement;
        }
        match expr.value {
            ast::Expr::LetBindings(_, ref mut expr) => ast::walk_mut_expr(self, expr),
            _ => ast::walk_mut_expr(self, expr),
        }
    }
}

pub struct ImplicitResolver<'a> {
    pub(crate) metadata: &'a mut FnvMap<Symbol, Arc<Metadata>>,
    environment: &'a TypecheckEnv<Type = RcType>,
    pub(crate) implicit_bindings: ImplicitBindings,
    pub(crate) implicit_vars: ScopedMap<Symbol, Level>,
    visited: ScopedMap<Box<[Symbol]>, Box<[RcType]>>,
    alias_resolver: resolve::AliasRemover<RcType>,
    is_implicit_memo: RefCell<FnvMap<SymbolKey, bool>>,
    path: Vec<TypedIdent<Symbol, RcType>>,
}

impl<'a> ImplicitResolver<'a> {
    pub fn new(
        environment: &'a TypecheckEnv<Type = RcType>,
        metadata: &'a mut FnvMap<Symbol, Arc<Metadata>>,
    ) -> ImplicitResolver<'a> {
        ImplicitResolver {
            metadata,
            environment,
            implicit_bindings: Default::default(),
            implicit_vars: ScopedMap::new(),
            visited: Default::default(),
            alias_resolver: resolve::AliasRemover::new(),
            is_implicit_memo: Default::default(),
            path: Vec::new(),
        }
    }

    pub fn on_stack_var(&mut self, subs: &Substitution<RcType>, id: &Symbol, typ: &RcType) {
        self.add_implicits_of_record(subs, id, typ);
    }

    pub fn add_implicits_of_record(
        &mut self,
        subs: &Substitution<RcType>,
        id: &Symbol,
        typ: &RcType,
    ) {
        self.alias_resolver.clear();

        self.path.clear();
        self.path.push(TypedIdent {
            name: id.clone(),
            typ: typ.clone(),
        });

        let meta = self.metadata.get(id).cloned();
        self.add_implicits_of_record_rec(subs, typ, meta.as_ref().map(|m| &**m), &mut Vec::new());
    }

    fn add_implicits_of_record_rec(
        &mut self,
        mut subs: &Substitution<RcType>,
        typ: &RcType,
        metadata: Option<&Metadata>,
        forall_params: &mut Vec<Generic<Symbol>>,
    ) {
        let typ = subs.real(typ);
        if metadata.is_none() && !typ.flags().contains(Flags::HAS_IMPLICIT) {
            return;
        }
        info!(
            "----- {} {}",
            metadata
                .and_then(|m| m.definition.as_ref())
                .map(|d| d.to_string())
                .unwrap_or_else(|| "N/A".to_string()),
            typ
        );

        // If we know what originally defined this value, and that has already been added don't
        // add it again to prevent ambiguities
        if let Some(metadata) = metadata {
            if let Some(ref definition) = metadata.definition {
                if self.implicit_bindings.definitions.contains_key(definition) {
                    return;
                }
            }
        }

        let opt = self.try_create_implicit(metadata, typ);

        let mut typ = typ.clone();
        if let Some(definition) = opt {
            let typ = subs.forall(forall_params.iter().cloned().collect(), typ.clone());

            self.implicit_bindings
                .insert(subs, definition, &self.path, &typ);
        }

        let forall_params_len_before = forall_params.len();

        while let Type::Forall(params, next) = &*typ {
            forall_params.extend(params.iter().cloned());
            typ = next.clone();
        }

        let raw_type =
            match self
                .alias_resolver
                .remove_aliases(&self.environment, &mut subs, typ.clone())
            {
                Ok(t) => t,
                // Don't recurse into self recursive aliases
                Err(_) => return,
            };
        match *raw_type {
            Type::Record(_) => {
                for field in raw_type.row_iter() {
                    let field_metadata = metadata
                        .and_then(|metadata| metadata.module.get(field.name.as_pretty_str()))
                        .map(|m| &**m);
                    if field_metadata.is_none() && !field.typ.flags().contains(Flags::HAS_IMPLICIT)
                    {
                        continue;
                    }

                    self.path.push(TypedIdent {
                        name: field.name.clone(),
                        typ: field.typ.clone(),
                    });

                    self.add_implicits_of_record_rec(
                        subs,
                        &field.typ,
                        field_metadata,
                        forall_params,
                    );

                    self.path.pop();
                }
            }
            _ => (),
        }
        forall_params.truncate(forall_params_len_before)
    }

    pub fn try_create_implicit<'m>(
        &self,
        metadata: Option<&'m Metadata>,
        typ: &RcType,
    ) -> Option<Option<&'m Symbol>> {
        let has_implicit_attribute =
            |metadata: &Metadata| metadata.get_attribute("implicit").is_some();
        let mut is_implicit = metadata.map(&has_implicit_attribute).unwrap_or(false);

        if !is_implicit {
            // Look at the type without any implicit arguments
            let mut iter = types::implicit_arg_iter(typ.remove_forall());
            for _ in iter.by_ref() {}
            is_implicit = iter
                .typ
                .remove_forall()
                .owned_name()
                .map_or(false, |typename| {
                    let mut is_implicit_memo = self.is_implicit_memo.borrow_mut();
                    *is_implicit_memo.entry(typename.clone()).or_insert_with(|| {
                        self.metadata
                            .get(&*typename)
                            .or_else(|| self.environment.get_metadata(&typename))
                            .map_or(false, |m| has_implicit_attribute(m))
                    })
                });
        }

        if is_implicit {
            Some(metadata.and_then(|m| m.definition.as_ref()))
        } else {
            None
        }
    }

    pub fn make_implicit_ident(&mut self, _typ: &RcType) -> Symbol {
        let name = Symbol::from("implicit_arg");

        let implicits_revision = Level(
            self.implicit_bindings
                .partition_insertions
                .len()
                .try_into()
                .unwrap(),
        );
        self.implicit_vars.insert(name.clone(), implicits_revision);
        name
    }

    pub fn enter_scope(&mut self) {
        self.implicit_bindings.enter_scope();
    }

    pub fn exit_scope(&mut self, subs: &Substitution<RcType>) {
        self.implicit_bindings.exit_scope(subs);
    }
}

pub fn resolve(tc: &mut Typecheck, expr: &mut SpannedExpr<Symbol>) {
    let mut visitor = ResolveImplicitsVisitor { tc };
    visitor.visit_expr(expr);
}

fn smaller(state: unify_type::State, new_type: &RcType, old_type: &RcType) -> Size {
    match unify_type::smaller(state.clone(), new_type, old_type) {
        Size::Smaller => match unify_type::smaller(state, old_type, new_type) {
            Size::Smaller => Size::Different,
            _ => Size::Smaller,
        },
        check => check,
    }
}
fn smallers(state: unify_type::State, new_types: &[RcType], old_types: &[RcType]) -> bool {
    if old_types.is_empty() {
        true
    } else {
        old_types
            .iter()
            .zip(new_types)
            .fold(Size::Equal, |acc, (old, new)| match acc {
                Size::Different => Size::Different,
                Size::Smaller => Size::Smaller,
                Size::Equal => smaller(state.clone(), new, old),
            })
            == Size::Smaller
    }
}
