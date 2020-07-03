use std::{fmt, rc::Rc, sync::Arc};

use {itertools::Itertools, smallvec::SmallVec};

use rpds;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent},
    error::AsDiagnostic,
    fnv::FnvMap,
    metadata::Metadata,
    pos::{self, BytePos, Span, Spanned},
    resolve,
    scoped_map::{self, ScopedMap},
    source::FileId,
    symbol::Symbol,
    types::{
        self, ArgType, BuiltinType, Flags, Generic, SymbolKey, Type, TypeContext, TypeExt, TypePtr,
    },
};

use crate::{
    substitution::Substitution,
    typ::RcType,
    typecheck::{TypeError, Typecheck},
    unify_type::{self, Size},
    TypecheckEnv,
};

fn spliterator<'a>(
    subs: &'a Substitution<RcType>,
    typ: &'a RcType,
) -> impl Iterator<Item = SymbolKey> + 'a {
    let mut current = Some(typ);
    std::iter::from_fn(move || {
        let typ = current?;
        let (symbol, next) = split_type(subs, typ)?;
        current = next;
        Some(symbol)
    })
}

fn split_type<'a>(
    subs: &'a Substitution<RcType>,
    typ: &'a RcType,
) -> Option<(SymbolKey, Option<&'a RcType>)> {
    let symbol = match &**subs.real(typ) {
        Type::App(id, args) => {
            return split_type(subs, id).map(|(key, _)| (key, args.get(0)));
        }
        Type::Forall(_, typ) | Type::Function(ArgType::Implicit, _, typ) => {
            return split_type(subs, typ)
        }
        Type::Function(ArgType::Explicit, ..) => {
            Some(SymbolKey::Ref(BuiltinType::Function.symbol()))
        }
        Type::Skolem(skolem) => Some(SymbolKey::Owned(skolem.name.clone())),
        Type::Ident(id) => Some(SymbolKey::Owned(id.name.clone())),
        Type::Alias(alias) => Some(SymbolKey::Owned(alias.name.clone())),
        Type::Builtin(builtin) => Some(SymbolKey::Ref(builtin.symbol())),
        _ => None,
    };
    symbol.map(|s| (s, None))
}

type ImplicitBinding = (Rc<[TypedIdent<Symbol, RcType>]>, RcType);

#[derive(Clone)]
pub struct Partition<T> {
    partition: rpds::HashTrieMap<SymbolKey, Partition<T>>,
    // The partitioning should be very fine grained so we usually have very few elements in each
    // partition
    rest: SmallVec<[T; 3]>,
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
                        .format_with(",", |i, f| f(&format_args!("{:?}", i)))
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
                        "{}: {}",
                        i.0.iter().map(|i| &i.name).format("."),
                        i.1
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
    fn insert(&mut self, subs: &Substitution<RcType>, typ: &RcType, value: T)
    where
        T: Clone,
    {
        let iter = spliterator(subs, typ);
        self.insert_(iter, &value);
    }

    fn insert_(&mut self, mut iter: impl Iterator<Item = SymbolKey>, value: &T) -> bool
    where
        T: Clone,
    {
        if let Some(symbol) = iter.next() {
            let mut partition = self.partition.get(&symbol).cloned().unwrap_or_default();
            partition.insert_(iter, value);
            partition.rest.push(value.clone());
            self.partition.insert_mut(symbol, partition);
            true
        } else {
            false
        }
    }

    fn get_candidates<'a>(
        &'a self,
        subs: &Substitution<RcType>,
        typ: &RcType,
    ) -> impl DoubleEndedIterator<Item = &'a T>
    where
        T: fmt::Debug,
    {
        let mut candidates = Vec::new();
        self.get_candidates_(subs, typ, &mut |t| candidates.push(t));
        candidates.into_iter()
    }

    fn get_candidates_<'a>(
        &'a self,
        subs: &Substitution<RcType>,
        typ: &RcType,
        consumer: &mut impl FnMut(&'a T),
    ) where
        T: fmt::Debug,
    {
        let mut partition = self;
        for symbol in spliterator(subs, typ) {
            match partition.partition.get(&symbol) {
                Some(bindings) => partition = bindings,
                None => break,
            }
        }
        partition.rest.iter().for_each(&mut *consumer);
    }
}

#[derive(Debug)]
pub(crate) struct ImplicitBindings {
    pub partition: Vec<Partition<ImplicitBinding>>,
    pub definitions: ScopedMap<Symbol, ()>,
}

impl Default for ImplicitBindings {
    fn default() -> Self {
        Self::new()
    }
}

impl ImplicitBindings {
    fn new() -> Self {
        Self {
            partition: vec![Default::default()],
            definitions: Default::default(),
        }
    }

    fn insert(
        &mut self,
        subs: &Substitution<RcType>,
        path: &[TypedIdent<Symbol, RcType>],
        typ: &RcType,
    ) {
        self.partition
            .last_mut()
            .unwrap()
            .insert(subs, typ, (Rc::from(&path[..]), typ.clone()));
    }

    pub fn partition(&self) -> &Partition<ImplicitBinding> {
        self.partition.last().expect("bindings")
    }

    pub fn enter_scope(&mut self) {
        if let Some(bind) = self.partition.last().cloned() {
            self.partition.push(bind);
        }
        self.definitions.enter_scope();
    }

    pub fn exit_scope(&mut self) {
        self.partition.pop();
        self.definitions.exit_scope();
    }
}

type Result<T> = ::std::result::Result<T, Error<RcType>>;

#[derive(Debug, Eq, PartialEq, Hash, Clone, Functor)]
pub struct Error<T> {
    pub kind: ErrorKind<T>,
    pub reason: rpds::ListSync<T>,
}

impl<I: fmt::Display + Clone> fmt::Display for Error<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl<I: fmt::Display + Clone> AsDiagnostic for Error<I> {
    fn as_diagnostic(&self, _map: &base::source::CodeMap) -> Diagnostic<FileId> {
        let mut diagnostic = Diagnostic::error().with_message(self.to_string());

        diagnostic.labels.extend(self.reason.iter().map(|reason| {
            Label::secondary(FileId::default(), Default::default()..Default::default())
                .with_message(format!(
                    "Required because of an implicit parameter of `{}`",
                    reason
                ))
        }));

        diagnostic
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Hash, Functor)]
pub struct AmbiguityEntry<T> {
    pub path: String,
    pub typ: T,
}

#[derive(Debug, Eq, PartialEq, Clone, Hash, Functor)]
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
    reason: rpds::ListSync<RcType>,
    constraint: RcType,
}

struct ResolveImplicitsVisitor<'a, 'b: 'a, 'ast> {
    tc: &'a mut Typecheck<'b, 'ast>,
}

impl<'a, 'b, 'ast> ResolveImplicitsVisitor<'a, 'b, 'ast> {
    fn resolve_implicit(
        &mut self,
        implicit_bindings: &Partition<ImplicitBinding>,
        expr: &SpannedExpr<Symbol>,
        id: &TypedIdent<Symbol, RcType>,
    ) -> Option<SpannedExpr<'ast, Symbol>> {
        debug!(
            "Resolving {} against:\n{}",
            id.typ,
            implicit_bindings
                .get_candidates(&self.tc.subs, &id.typ,)
                .map(|t| &t.1)
                .format("\n")
        );
        self.tc.implicit_resolver.visited.clear();
        let span = expr.span;
        let mut to_resolve = Vec::new();
        match self.find_implicit(
            implicit_bindings,
            &mut to_resolve,
            &Demand {
                reason: Default::default(),
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
                    implicit_bindings,
                    0,
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
                                    .map_or_else(Default::default, |demand| demand.reason.clone()),
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
        implicit_bindings: &Partition<ImplicitBinding>,
        level: u32,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<'ast, Symbol>>> {
        self.resolve_implicit_application_(implicit_bindings, level, span, path, to_resolve)
            .map_err(|mut err| {
                if let ErrorKind::LoopInImplicitResolution(ref mut paths) = err.kind {
                    paths.push(path.iter().map(|id| &id.name).format(".").to_string());
                }
                err
            })
    }

    fn resolve_implicit_application_(
        &mut self,
        implicit_bindings: &Partition<ImplicitBinding>,
        level: u32,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<'ast, Symbol>>> {
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
                        self.tc.ast_arena.alloc(expr),
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
                        .find_implicit(implicit_bindings, &mut to_resolve, demand)
                        .and_then(|path| {
                            debug!("Success! Resolving arguments");
                            self.resolve_implicit_application(
                                implicit_bindings,
                                level + 1,
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
                    Expr::app(self.tc.ast_arena, func, resolved_arguments),
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
        implicit_bindings: &Partition<ImplicitBinding>,
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
    ) -> Result<Rc<[TypedIdent<Symbol, RcType>]>> {
        let mut candidates = implicit_bindings
            .get_candidates(&self.tc.subs, &demand.constraint)
            .rev();
        let mut snapshot = Some(self.tc.subs.snapshot());
        let found_candidate = candidates.by_ref().find(|x| {
            let (path, typ) = &*x;
            if self.try_resolve_implicit(path, to_resolve, demand, typ) {
                true
            } else {
                self.tc.subs.rollback_to(snapshot.take().unwrap());
                snapshot = Some(self.tc.subs.snapshot());
                false
            }
        });
        match found_candidate {
            Some(x) => {
                self.tc.subs.commit(snapshot.unwrap());
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
                        let snapshot = self.tc.subs.snapshot();
                        let b = self.try_resolve_implicit(path, &mut Vec::new(), demand, typ);
                        self.tc.subs.rollback_to(snapshot);
                        b
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

impl<'a, 'b, 'c, 'ast> MutVisitor<'c, 'ast> for ResolveImplicitsVisitor<'a, 'b, 'ast> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &mut SpannedExpr<'ast, Symbol>) {
        let mut replacement = None;
        if let Expr::Ident(ref id) = expr.value {
            let implicit_vars = self
                .tc
                .implicit_resolver
                .implicit_vars
                .get(&id.name)
                .cloned();
            if let Some(implicit_vars) = implicit_vars {
                let typ = id.typ.clone();
                let id = TypedIdent {
                    name: id.name.clone(),
                    typ: typ,
                };
                replacement = self.resolve_implicit(&implicit_vars, expr, &id);
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
    environment: &'a dyn TypecheckEnv<Type = RcType>,
    pub(crate) implicit_bindings: ImplicitBindings,
    pub(crate) implicit_vars: ScopedMap<Symbol, Partition<ImplicitBinding>>,
    visited: ScopedMap<Box<[Symbol]>, Box<[RcType]>>,
    alias_resolver: resolve::AliasRemover<RcType>,
    path: Vec<TypedIdent<Symbol, RcType>>,
}

impl<'a> ImplicitResolver<'a> {
    pub fn new(
        environment: &'a dyn TypecheckEnv<Type = RcType>,
        metadata: &'a mut FnvMap<Symbol, Arc<Metadata>>,
    ) -> ImplicitResolver<'a> {
        ImplicitResolver {
            metadata,
            environment,
            implicit_bindings: Default::default(),
            implicit_vars: ScopedMap::new(),
            visited: Default::default(),
            alias_resolver: resolve::AliasRemover::new(),
            path: Vec::new(),
        }
    }

    pub fn on_stack_var(&mut self, subs: &Substitution<RcType>, id: &Symbol, typ: &RcType) {
        self.alias_resolver.clear();

        self.path.clear();
        self.path.push(TypedIdent {
            name: id.clone(),
            typ: typ.clone(),
        });

        let meta = self.metadata.get(id).cloned();

        self.add_implicits_of_ident(subs, typ, meta.as_ref().map(|m| &**m), &mut Vec::new());
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

    fn add_implicits_of_ident(
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

        // If we know what originally defined this value, and that has already been added don't
        // add it again to prevent ambiguities
        if let Some(metadata) = metadata {
            if let Some(ref definition) = metadata.definition {
                if self
                    .implicit_bindings
                    .definitions
                    .insert(definition.clone(), ())
                {
                    return;
                }
            }
        }

        let opt = self.try_create_implicit(metadata, typ);

        if let Some(_) = opt {
            let typ = subs.forall(forall_params.iter().cloned().collect(), typ.clone());

            self.implicit_bindings.insert(subs, &self.path, &typ);

            self.add_implicits_of_record_rec(subs, &typ, metadata, forall_params)
        }
    }

    fn add_implicits_of_record_rec(
        &mut self,
        mut subs: &Substitution<RcType>,
        typ: &RcType,
        metadata: Option<&Metadata>,
        forall_params: &mut Vec<Generic<Symbol>>,
    ) {
        let forall_params_len_before = forall_params.len();

        let mut typ = typ.clone();
        while let Type::Forall(params, next) = &*typ {
            forall_params.extend(params.iter().cloned());
            typ = next.clone();
        }

        let t = self.alias_resolver.remove_aliases_predicate(
            &self.environment,
            &mut subs,
            typ.clone(),
            |alias| {
                alias
                    .unresolved_type()
                    .flags()
                    .contains(Flags::HAS_IMPLICIT)
            },
        );
        let raw_type = match t {
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

                    self.add_implicits_of_ident(subs, &field.typ, field_metadata, forall_params);

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
        // Look at the type without any implicit arguments
        let mut iter = types::implicit_arg_iter(typ.remove_forall());
        for _ in iter.by_ref() {}
        let is_implicit = iter
            .typ
            .remove_forall()
            .applied_alias()
            .map_or(false, |alias| alias.is_implicit())
            || metadata
                .and_then(|metadata: &Metadata| metadata.get_attribute("implicit"))
                .is_some();

        if is_implicit {
            Some(metadata.and_then(|m| m.definition.as_ref()))
        } else {
            None
        }
    }

    pub fn make_implicit_ident(&mut self, _typ: &RcType) -> Symbol {
        let name = Symbol::from("implicit_arg");

        let implicits_revision = self.implicit_bindings.partition().clone();

        self.implicit_vars.insert(name.clone(), implicits_revision);
        name
    }

    pub fn enter_scope(&mut self) {
        self.implicit_bindings.enter_scope();
    }

    pub fn exit_scope(&mut self) {
        self.implicit_bindings.exit_scope();
    }
}

pub fn resolve<'ast>(tc: &mut Typecheck<'_, 'ast>, expr: &mut SpannedExpr<'ast, Symbol>) {
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

#[cfg(test)]
mod tests {
    use super::*;

    use base::{ast::KindedIdent, kind::Kind, types::SharedInterner};

    use crate::tests::*;

    #[test]
    fn spliterator_test() {
        let interner = SharedInterner::default();
        let subs = Substitution::new(Kind::typ(), interner);

        let a = intern("A");
        let b = intern("B");

        let typ = Type::app(
            Type::ident(KindedIdent {
                name: a.clone(),
                typ: Kind::typ(),
            }),
            collect![Type::ident(KindedIdent {
                name: b.clone(),
                typ: Kind::typ()
            })],
        );
        assert_eq!(
            spliterator(&subs, &typ).collect::<Vec<_>>(),
            vec![SymbolKey::Owned(a.clone()), SymbolKey::Owned(b.clone())]
        );

        let typ = Type::app(
            Type::ident(KindedIdent {
                name: a.clone(),
                typ: Kind::typ(),
            }),
            collect![Type::app(
                Type::ident(KindedIdent {
                    name: b.clone(),
                    typ: Kind::typ(),
                }),
                collect![Type::generic(Generic::new(intern("c"), Kind::typ()))]
            )],
        );
        assert_eq!(
            spliterator(&subs, &typ).collect::<Vec<_>>(),
            vec![SymbolKey::Owned(a), SymbolKey::Owned(b)]
        );
    }
}
