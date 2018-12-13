use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use itertools::{Either, Itertools};

use rpds;

use codespan_reporting::{Diagnostic, Label};

use base::ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent};
use base::error::AsDiagnostic;
use base::fnv::FnvMap;
use base::metadata::Metadata;
use base::pos::{self, BytePos, Span, Spanned};
use base::resolve;
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolRef};
use base::types::{self, ArcType, ArgType, BuiltinType, Type};

use substitution::Substitution;
use typecheck::{TypeError, Typecheck, TypecheckEnv};

const MAX_IMPLICIT_LEVEL: u32 = 20;

impl SymbolKey {
    pub fn new(typ: &ArcType) -> Option<SymbolKey> {
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

type ImplicitBinding = (Vec<TypedIdent<Symbol>>, ArcType);
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

    fn insert(&mut self, definition: Option<&Symbol>, path: Vec<TypedIdent<Symbol>>, typ: ArcType) {
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
        F: FnMut(&Symbol) -> Option<ArcType>,
    {
        fn update_vec<F>(vec: &mut ImplicitVector, mut f: F) -> bool
        where
            F: FnMut(&Symbol) -> Option<ArcType>,
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

    fn iter<'a>(&'a self, typ: &ArcType) -> impl DoubleEndedIterator<Item = &'a ImplicitBinding> {
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

type Result<T> = ::std::result::Result<T, Error<Symbol>>;

#[derive(Debug, PartialEq)]
pub struct Error<I> {
    pub kind: ErrorKind<I>,
    pub reason: rpds::List<ArcType<I>>,
}

impl<I: fmt::Display + AsRef<str> + Clone> fmt::Display for Error<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl<I: fmt::Display + AsRef<str> + Clone> AsDiagnostic for Error<I> {
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

#[derive(Debug, PartialEq)]
pub enum ErrorKind<I> {
    /// An implicit parameter were not possible to resolve
    MissingImplicit(ArcType<I>),
    LoopInImplicitResolution(Vec<String>),
    AmbiguousImplicit(Vec<(String, ArcType<I>)>),
}

impl<I: fmt::Display + AsRef<str> + Clone> fmt::Display for ErrorKind<I> {
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
                    .format_with(", ", |&(ref path, ref typ), fmt| fmt(&format_args!(
                        "{}: {}",
                        path, typ
                    )))
            ),
        }
    }
}

struct Demand {
    reason: rpds::List<ArcType>,
    constraint: ArcType,
}

struct ResolveImplicitsVisitor<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
}

impl<'a, 'b> ResolveImplicitsVisitor<'a, 'b> {
    fn resolve_implicit_application(
        &mut self,
        level: u32,
        implicit_bindings: &ImplicitBindings,
        span: Span<BytePos>,
        path: &[TypedIdent<Symbol>],
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
        path: &[TypedIdent<Symbol>],
        to_resolve: &[Demand],
    ) -> Result<Option<SpannedExpr<Symbol>>> {
        match to_resolve.first() {
            Some(demand) if level > MAX_IMPLICIT_LEVEL => {
                return Err(Error {
                    kind: ErrorKind::LoopInImplicitResolution(Vec::new()),
                    reason: demand.reason.clone(),
                });
            }
            _ => (),
        }

        let base_ident = path[0].clone();
        let func = path[1..].iter().fold(
            pos::spanned(span, Expr::Ident(base_ident)),
            |expr, ident| {
                pos::spanned(
                    expr.span,
                    Expr::Projection(Box::new(expr), ident.name.clone(), ident.typ.clone()),
                )
            },
        );

        Ok(if to_resolve.is_empty() {
            Some(func)
        } else {
            let resolved_arguments = to_resolve
                .iter()
                .filter_map(|demand| {
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

    fn try_implicit(
        &mut self,
        path: &[TypedIdent<Symbol>],
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
        typ: &ArcType,
    ) -> bool {
        debug!(
            "Trying implicit `{}` : {}",
            path.iter().map(|id| &id.name).format("."),
            typ,
        );

        let typ = self.tc.new_skolem_scope(typ);
        let typ = self.tc.instantiate_generics(&typ);
        to_resolve.clear();
        let mut iter = types::implicit_arg_iter(&typ);
        to_resolve.extend(iter.by_ref().cloned().map(|constraint| Demand {
            reason: demand.reason.push_front(typ.clone()),
            constraint,
        }));

        let state =
            ::unify_type::State::new(&self.tc.environment, &self.tc.subs, &self.tc.type_cache);
        ::unify_type::subsumes(
            &self.tc.subs,
            &mut ScopedMap::new(),
            0,
            state,
            &demand.constraint,
            &iter.typ,
        )
        .is_ok()
    }

    fn find_implicit<'c>(
        &mut self,
        implicit_bindings: &'c ImplicitBindings,
        to_resolve: &mut Vec<Demand>,
        demand: &Demand,
    ) -> Result<&'c [TypedIdent<Symbol>]> {
        let mut iter = implicit_bindings.iter(&demand.constraint).rev();
        let found_candidate = iter
            .by_ref()
            .find(|&&(ref path, ref typ)| self.try_implicit(path, to_resolve, demand, typ));
        match found_candidate {
            Some(candidate) => {
                let mut additional_candidates: Vec<_> = iter
                    .filter(|&&(ref path, ref typ)| {
                        self.try_implicit(path, &mut Vec::new(), demand, typ)
                    })
                    .map(|bind| {
                        (
                            bind.0.iter().map(|id| &id.name).format(".").to_string(),
                            bind.1.clone(),
                        )
                    })
                    .collect();
                if additional_candidates.is_empty() {
                    Ok(&candidate.0)
                } else {
                    additional_candidates.push((
                        candidate
                            .0
                            .iter()
                            .map(|id| &id.name)
                            .format(".")
                            .to_string(),
                        candidate.1.clone(),
                    ));
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
        if let Expr::Ident(ref mut id) = expr.value {
            let implicit_bindings = self
                .tc
                .implicit_resolver
                .implicit_vars
                .get(&id.name)
                .cloned();
            if let Some(implicit_bindings) = implicit_bindings {
                debug!(
                    "Resolving {} against:\n{}",
                    id.typ,
                    implicit_bindings.iter(&id.typ).map(|t| &t.1).format("\n")
                );
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

                        replacement = match resolution_result {
                            Some(Ok(replacement)) => Some(replacement),
                            Some(Err(err)) => {
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
                                            .map_or_else(rpds::List::new, |demand| {
                                                demand.reason.clone()
                                            }),
                                    })
                                    .into(),
                                });
                                None
                            }
                        };
                    }
                    Err(err) => {
                        self.tc.errors.push(Spanned {
                            span: expr.span,
                            value: TypeError::UnableToResolveImplicit(err).into(),
                        });
                    }
                }
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
    environment: &'a TypecheckEnv,
    pub(crate) implicit_bindings: Vec<ImplicitBindings>,
    implicit_vars: ScopedMap<Symbol, ImplicitBindings>,
}

impl<'a> ImplicitResolver<'a> {
    pub fn new(
        environment: &'a TypecheckEnv,
        metadata: &'a mut FnvMap<Symbol, Metadata>,
    ) -> ImplicitResolver<'a> {
        ImplicitResolver {
            metadata,
            environment,
            implicit_bindings: Vec::new(),
            implicit_vars: ScopedMap::new(),
        }
    }

    pub fn on_stack_var(&mut self, id: &Symbol, typ: &ArcType) {
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
        subs: &Substitution<ArcType>,
        id: &Symbol,
        typ: &ArcType,
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

        let typ = ::unify_type::top_skolem_scope(subs, subs.real(typ));
        let ref typ = typ.instantiate_generics(&mut FnvMap::default(), || subs.new_var());
        let raw_type = match alias_resolver.remove_aliases(&self.environment, typ.clone()) {
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
        typ: &ArcType,
        path: &mut Vec<TypedIdent<Symbol>>,
        consumer: &mut FnMut(Option<&Symbol>, Vec<TypedIdent<Symbol>>, &ArcType),
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

    pub fn make_implicit_ident(&mut self, _typ: &ArcType) -> Symbol {
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
