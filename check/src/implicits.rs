use std::{
    borrow::Borrow,
    cell::RefCell,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};

use itertools::{Either, Itertools};

use rpds;

use codespan_reporting::{Diagnostic, Label};

use crate::base::{
    ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent},
    error::AsDiagnostic,
    fnv::FnvMap,
    metadata::{Metadata, MetadataEnv},
    pos::{self, BytePos, Span, Spanned},
    resolve,
    scoped_map::{self, ScopedMap},
    symbol::{Symbol, SymbolRef},
    types::{self, ArcType, ArgType, BuiltinType, SharedInterner, Type, TypeExt},
};

use crate::{
    substitution::Substitution,
    typ::{PtrEq, RcType},
    typecheck::{TypeError, Typecheck},
    unify_type::{self, Size},
    ArcTypeCacher, TypecheckEnv,
};

impl SymbolKey {
    pub fn new(typ: &RcType) -> Option<SymbolKey> {
        match **typ {
            Type::App(ref id, _) => SymbolKey::new(id),
            Type::Function(ArgType::Implicit, _, ref ret_type) => SymbolKey::new(ret_type),
            Type::Function(ArgType::Explicit, ..) => {
                Some(SymbolKey::Ref(BuiltinType::Function.symbol()))
            }
            Type::Ident(ref id) => Some(SymbolKey::Owned(id.clone())),
            Type::Alias(ref alias) => Some(SymbolKey::Owned(alias.name.clone())),
            Type::Builtin(ref builtin) => Some(SymbolKey::Ref(builtin.symbol())),
            Type::Forall(_, ref typ, _) => SymbolKey::new(typ),
            _ => None,
        }
    }
}

#[derive(Eq, Clone, Debug)]
pub enum SymbolKey {
    Owned(Symbol),
    Ref(&'static SymbolRef),
}

impl Hash for SymbolKey {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        Borrow::<SymbolRef>::borrow(self).hash(state)
    }
}

impl PartialEq for SymbolKey {
    fn eq(&self, other: &Self) -> bool {
        Borrow::<SymbolRef>::borrow(self) == Borrow::<SymbolRef>::borrow(other)
    }
}

impl PartialOrd for SymbolKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Borrow::<SymbolRef>::borrow(self).partial_cmp(Borrow::<SymbolRef>::borrow(other))
    }
}

impl Ord for SymbolKey {
    fn cmp(&self, other: &Self) -> Ordering {
        Borrow::<SymbolRef>::borrow(self).cmp(Borrow::<SymbolRef>::borrow(other))
    }
}

impl Borrow<SymbolRef> for SymbolKey {
    fn borrow(&self) -> &SymbolRef {
        match *self {
            SymbolKey::Owned(ref s) => s,
            SymbolKey::Ref(s) => s,
        }
    }
}

type ImplicitBinding = (Vec<TypedIdent<Symbol, RcType>>, RcType);
type ImplicitVector = ::rpds::Vector<ImplicitBinding>;

#[derive(Clone, Default, Debug)]
pub(crate) struct ImplicitBindings {
    partioned: ::rpds::RedBlackTreeMap<SymbolKey, ImplicitVector>,
    rest: ImplicitVector,
    definitions: ::rpds::RedBlackTreeSet<Symbol>,
}

impl ImplicitBindings {
    fn new() -> ImplicitBindings {
        ImplicitBindings::default()
    }

    fn insert(
        &mut self,
        definition: Option<&Symbol>,
        path: Vec<TypedIdent<Symbol, RcType>>,
        typ: RcType,
    ) {
        if let Some(definition) = definition {
            self.definitions.insert_mut(definition.clone());
        }

        match SymbolKey::new(&typ) {
            Some(symbol) => {
                let mut vec = self.partioned.get(&symbol).cloned().unwrap_or_default();
                vec.push_back_mut((path, typ));
                self.partioned.insert_mut(symbol, vec);
            }
            None => self.rest.push_back_mut((path, typ)),
        }
    }

    pub fn update<F>(&mut self, mut f: F)
    where
        F: FnMut(&Symbol) -> Option<RcType>,
    {
        fn update_vec<F>(vec: &mut ImplicitVector, mut f: F) -> bool
        where
            F: FnMut(&Symbol) -> Option<RcType>,
        {
            let mut updated = false;

            for i in 0..vec.len() {
                let opt = {
                    let bind = vec.get(i).unwrap();
                    if bind.0.len() == 1 {
                        let typ = f(&bind.0[0].name).unwrap();
                        Some((bind.0.clone(), typ))
                    } else {
                        None
                    }
                };
                if let Some(new) = opt {
                    vec.set_mut(i, new);
                    updated = true;
                }
            }
            updated
        }

        for (key, vec) in &self.partioned.clone() {
            let mut vec = vec.clone();
            if update_vec(&mut vec, &mut f) {
                self.partioned.insert_mut(key.clone(), vec);
            }
        }

        update_vec(&mut self.rest, &mut f);
    }

    fn get_candidates<'a>(
        &'a self,
        typ: &RcType,
    ) -> impl DoubleEndedIterator<Item = &'a ImplicitBinding> {
        match SymbolKey::new(&typ) {
            Some(symbol) => Either::Left(self.partioned.get(&symbol).unwrap_or(&self.rest).iter()),
            None => Either::Right(
                self.rest
                    .iter()
                    .chain(self.partioned.values().flat_map(|x| x.iter())),
            ),
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
        implicit_bindings: &ImplicitBindings,
        expr: &SpannedExpr<Symbol>,
        id: &TypedIdent<Symbol, RcType>,
    ) -> Option<SpannedExpr<Symbol>> {
        debug!(
            "Resolving {} against:\n{}",
            id.typ,
            implicit_bindings
                .get_candidates(&id.typ)
                .map(|t| &t.1)
                .format("\n")
        );
        self.tc.implicit_resolver.visited.clear();
        let span = expr.span;
        let mut to_resolve = Vec::new();
        match self.find_implicit(
            &implicit_bindings,
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
                    &implicit_bindings,
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
        implicit_bindings: &ImplicitBindings,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol, RcType>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<Symbol>>> {
        self.resolve_implicit_application_(level, implicit_bindings, span, path, to_resolve)
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
        implicit_bindings: &ImplicitBindings,
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
                        .find_implicit(implicit_bindings, &mut to_resolve, demand)
                        .and_then(|path| {
                            debug!("Success! Resolving arguments");
                            self.resolve_implicit_application(
                                level + 1,
                                implicit_bindings,
                                span,
                                path,
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

        let binding_type = self.tc.new_skolem_scope(binding_type);
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

    fn find_implicit<'c>(
        &mut self,
        implicit_bindings: &'c ImplicitBindings,
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
    ) -> Result<&'c [TypedIdent<Symbol, RcType>]> {
        let mut candidates = implicit_bindings.get_candidates(&demand.constraint).rev();
        let found_candidate = candidates
            .by_ref()
            .find(|&&(ref path, ref typ)| self.try_resolve_implicit(path, to_resolve, demand, typ));
        match found_candidate {
            Some((candidate_path, candidate_type)) => {
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
                    .filter(|&&(ref path, ref typ)| {
                        self.try_resolve_implicit(path, &mut Vec::new(), demand, typ)
                    })
                    .map(|bind| AmbiguityEntry {
                        path: bind.0.iter().map(|id| &id.name).format(".").to_string(),
                        typ: bind.1.clone(),
                    })
                    .collect();
                if additional_candidates.is_empty() {
                    Ok(&candidate_path)
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
            let implicit_bindings = self
                .tc
                .implicit_resolver
                .implicit_vars
                .get(&id.name)
                .cloned();
            if let Some(implicit_bindings) = implicit_bindings {
                let typ = self.tc.subs.arc_real(&id.typ).clone();
                let id = TypedIdent {
                    name: id.name.clone(),
                    typ: typ,
                };
                replacement = self.resolve_implicit(&implicit_bindings, expr, &id);
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
    pub(crate) metadata: &'a mut FnvMap<Symbol, Metadata>,
    environment: ArcTypeCacher<'a>,
    pub(crate) implicit_bindings: Vec<ImplicitBindings>,
    implicit_vars: ScopedMap<Symbol, ImplicitBindings>,
    visited: ScopedMap<Box<[Symbol]>, Box<[RcType]>>,
}

impl<'a> ImplicitResolver<'a> {
    pub fn new(
        environment: &'a TypecheckEnv<Type = ArcType>,
        type_interner: Rc<RefCell<FnvMap<PtrEq<ArcType>, RcType>>>,
        interner: SharedInterner<RcType>,
        metadata: &'a mut FnvMap<Symbol, Metadata>,
    ) -> ImplicitResolver<'a> {
        ImplicitResolver {
            metadata,
            environment: ArcTypeCacher::new(environment, type_interner, interner),
            implicit_bindings: Vec::new(),
            implicit_vars: ScopedMap::new(),
            visited: Default::default(),
        }
    }

    pub fn on_stack_var(&mut self, id: &Symbol, typ: &RcType) {
        if self.implicit_bindings.is_empty() {
            self.implicit_bindings.push(ImplicitBindings::new());
        }
        let mut bindings = self.implicit_bindings.last_mut().unwrap().clone();
        let metadata = self.metadata.get(id);
        self.try_add_implicit(
            &id,
            metadata,
            &typ,
            &mut Vec::new(),
            &mut |definition, path, implicit_type| {
                bindings.insert(definition, path, implicit_type.clone());
            },
        );
        *self.implicit_bindings.last_mut().unwrap() = bindings;
    }

    pub fn add_implicits_of_record(
        &mut self,
        mut subs: &Substitution<RcType>,
        id: &Symbol,
        typ: &RcType,
    ) {
        info!("Trying to resolve implicit {}", typ);

        if self.implicit_bindings.is_empty() {
            self.implicit_bindings.push(ImplicitBindings::new());
        }
        let mut bindings = self.implicit_bindings.last().unwrap().clone();

        let mut path = vec![TypedIdent {
            name: id.clone(),
            typ: typ.clone(),
        }];
        let metadata = self.metadata.get(id);
        let mut alias_resolver = resolve::AliasRemover::new();

        let typ = crate::unify_type::top_skolem_scope(subs, subs.real(typ));
        let ref typ = typ.instantiate_generics(&mut subs, &mut FnvMap::default());
        let raw_type =
            match alias_resolver.remove_aliases(&self.environment, &mut subs, typ.clone()) {
                Ok(t) => t,
                // Don't recurse into self recursive aliases
                Err(_) => return,
            };
        match *raw_type {
            Type::Record(_) => {
                for field in raw_type.row_iter() {
                    let field_metadata = metadata
                        .as_ref()
                        .and_then(|metadata| metadata.module.get(field.name.declared_name()));

                    self.try_add_implicit(
                        &field.name,
                        field_metadata,
                        &field.typ,
                        &mut path,
                        &mut |definition, path, implicit_type| {
                            bindings.insert(definition, path, implicit_type.clone());
                        },
                    );
                }
            }
            _ => (),
        }
        *self.implicit_bindings.last_mut().unwrap() = bindings;
    }

    pub fn try_add_implicit(
        &self,
        id: &Symbol,
        metadata: Option<&Metadata>,
        typ: &RcType,
        path: &mut Vec<TypedIdent<Symbol, RcType>>,
        consumer: &mut FnMut(Option<&Symbol>, Vec<TypedIdent<Symbol, RcType>>, &RcType),
    ) {
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
                .name()
                .and_then(|typename| {
                    self.metadata
                        .get(typename)
                        .or_else(|| self.environment.get_metadata(typename))
                        .map(has_implicit_attribute)
                })
                .unwrap_or(false);
        }

        if is_implicit {
            // If we know what originally defined this value, and that has already been added don't
            // add it again to prevent ambiguities
            if let Some(metadata) = metadata {
                if let Some(ref definition) = metadata.definition {
                    if self
                        .implicit_bindings
                        .last()
                        .unwrap()
                        .definitions
                        .contains(definition)
                    {
                        return;
                    }
                }
            }

            let mut path = path.clone();
            path.push(TypedIdent {
                name: id.clone(),
                typ: typ.clone(),
            });
            consumer(metadata.and_then(|m| m.definition.as_ref()), path, typ);
        }
    }

    pub fn make_implicit_ident(&mut self, _typ: &RcType) -> Symbol {
        let name = Symbol::from("implicit_arg");

        let implicits = self.implicit_bindings.last().unwrap().clone();
        self.implicit_vars.insert(name.clone(), implicits);
        name
    }

    pub fn enter_scope(&mut self) {
        let bindings = self.implicit_bindings.last().cloned().unwrap_or_default();
        self.implicit_bindings.push(bindings);
    }

    pub fn exit_scope(&mut self) {
        self.implicit_bindings.pop();
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
