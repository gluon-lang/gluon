use itertools::Itertools;

use base::ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent};
use base::fnv::FnvMap;
use base::metadata::Metadata;
use base::types::{self, ArcType, Type};
use base::pos::{self, BytePos, Span, Spanned};
use base::resolve;
use base::scoped_map::ScopedMap;
use base::symbol::Symbol;

use typecheck::{TcResult, TypeError, Typecheck, TypecheckEnv};
use substitution::Substitution;

const MAX_IMPLICIT_LEVEL: u32 = 20;

type ImplicitBindings = ::rpds::Vector<(Vec<TypedIdent<Symbol>>, ArcType)>;

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
        to_resolve: &[ArcType],
    ) -> TcResult<Option<SpannedExpr<Symbol>>> {
        self.resolve_implicit_application_(level, implicit_bindings, span, path, to_resolve)
            .map_err(|mut err| {
                if let TypeError::LoopInImplicitResolution(ref mut paths) = err {
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
        to_resolve: &[ArcType],
    ) -> TcResult<Option<SpannedExpr<Symbol>>> {
        if level > MAX_IMPLICIT_LEVEL {
            return Err(TypeError::LoopInImplicitResolution(Vec::new()));
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
                .filter_map(|expected_type| {
                    let mut to_resolve = Vec::new();
                    let result =
                        self.find_implicit(implicit_bindings, &mut to_resolve, expected_type)
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
                .collect::<TcResult<Vec<_>>>()?;
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
        to_resolve: &mut Vec<ArcType>,
        expected_type: &ArcType,
        typ: &ArcType,
    ) -> bool {
        debug!(
            "Trying implicit `{}` : {}",
            path.iter().map(|id| &id.name).format("."),
            typ
        );

        let typ = self.tc.new_skolem_scope(typ);
        let typ = self.tc.instantiate_generics(&typ);
        to_resolve.clear();
        let mut iter = types::implicit_arg_iter(&typ);
        to_resolve.extend(iter.by_ref().cloned());

        let state = ::unify_type::State::new(&self.tc.environment, &self.tc.subs);
        ::unify_type::subsumes(
            &self.tc.subs,
            &mut ScopedMap::new(),
            0,
            state,
            &expected_type,
            &iter.typ,
        ).is_ok()
    }

    fn find_implicit<'c>(
        &mut self,
        implicit_bindings: &'c ImplicitBindings,
        to_resolve: &mut Vec<ArcType>,
        expected_type: &ArcType,
    ) -> TcResult<&'c [TypedIdent<Symbol>]> {
        let mut iter = implicit_bindings.iter().rev();
        let found_candidate = iter.by_ref()
            .find(|&&(ref path, ref typ)| self.try_implicit(path, to_resolve, expected_type, typ));
        match found_candidate {
            Some(candidate) => {
                let mut additional_candidates: Vec<_> = iter.filter(|&&(ref path, ref typ)| {
                    self.try_implicit(path, &mut Vec::new(), expected_type, typ)
                }).map(|bind| {
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
                    Err(TypeError::AmbiguousImplicit(additional_candidates))
                }
            }
            None => Err(TypeError::UnableToResolveImplicit(
                expected_type.clone(),
                implicit_bindings
                    .iter()
                    .map(|&(ref path, _)| path.iter().map(|id| &id.name).format(".").to_string())
                    .collect(),
            )),
        }
    }
}

impl<'a, 'b, 'c> MutVisitor<'c> for ResolveImplicitsVisitor<'a, 'b> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
        let mut replacement = None;
        if let Expr::Ident(ref mut id) = expr.value {
            let implicit_bindings = self.tc
                .implicit_resolver
                .implicit_vars
                .get(&id.name)
                .cloned();
            if let Some(implicit_bindings) = implicit_bindings {
                debug!(
                    "Resolving {} against:\n{}",
                    id.typ,
                    implicit_bindings.iter().map(|t| &t.1).format("\n")
                );
                let span = expr.span;
                let mut to_resolve = Vec::new();
                match self.find_implicit(&implicit_bindings, &mut to_resolve, &id.typ) {
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
                                self.tc.error(span, err);
                                None
                            }
                            None => {
                                debug!("UnableToResolveImplicit {:?} {}", id.name, id.typ);
                                self.tc.errors.push(Spanned {
                                    span: expr.span,
                                    value: TypeError::UnableToResolveImplicit(
                                        id.typ.clone(),
                                        implicit_bindings
                                            .iter()
                                            .map(|&(ref path, _)| {
                                                path.iter()
                                                    .map(|id| &id.name)
                                                    .format(".")
                                                    .to_string()
                                            })
                                            .collect(),
                                    ).into(),
                                });
                                None
                            }
                        };
                    }
                    Err(err) => {
                        self.tc.error(span, err);
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
    pub(crate) metadata: FnvMap<Symbol, Metadata>,
    environment: &'a TypecheckEnv,
    pub(crate) implicit_bindings: Vec<ImplicitBindings>,
    implicit_vars: ScopedMap<Symbol, ImplicitBindings>,
}

impl<'a> ImplicitResolver<'a> {
    pub fn new(environment: &'a TypecheckEnv) -> ImplicitResolver<'a> {
        ImplicitResolver {
            metadata: FnvMap::default(),
            environment,
            implicit_bindings: Vec::new(),
            implicit_vars: ScopedMap::new(),
        }
    }

    pub fn on_stack_var(&mut self, id: &Symbol, typ: &ArcType) {
        if self.implicit_bindings.is_empty() {
            self.implicit_bindings.push(::rpds::Vector::new());
        }
        let mut bindings = self.implicit_bindings.last_mut().unwrap().clone();
        let metadata = self.metadata.get(id);
        self.try_add_implicit(
            &id,
            metadata,
            &typ,
            &mut Vec::new(),
            &mut |path, implicit_type| {
                bindings = bindings.push_back((path, implicit_type.clone()));
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
            self.implicit_bindings.push(::rpds::Vector::new());
        }
        let mut bindings = self.implicit_bindings.last_mut().unwrap().clone();

        let mut path = Vec::new();
        let metadata = self.metadata.get(id);
        let mut alias_resolver = resolve::AliasRemover::new();

        let typ = ::unify_type::top_skolem_scope(subs, subs.real(typ));
        let ref typ = typ.instantiate_generics(&mut FnvMap::default());
        let raw_type = match alias_resolver.remove_aliases(&self.environment, typ.clone()) {
            Ok(t) => t,
            // Don't recurse into self recursive aliases
            Err(_) => return,
        };
        match *raw_type {
            Type::Record(_) => for field in raw_type.row_iter() {
                let field_metadata = metadata
                    .as_ref()
                    .and_then(|metadata| metadata.module.get(field.name.declared_name()));

                path.push(TypedIdent {
                    name: id.clone(),
                    typ: typ.clone(),
                });
                self.try_add_implicit(
                    &field.name,
                    field_metadata,
                    &field.typ,
                    &mut path,
                    &mut |path, implicit_type| {
                        bindings = bindings.push_back((path, implicit_type.clone()));
                    },
                );
                path.pop();
            },
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
        consumer: &mut FnMut(Vec<TypedIdent<Symbol>>, &ArcType),
    ) {
        let has_implicit_attribute = |metadata: &Metadata| {
            metadata
                .comment
                .as_ref()
                .map(|comment| ::metadata::attributes(&comment).any(|(key, _)| key == "implicit"))
        };
        let mut is_implicit = metadata.and_then(&has_implicit_attribute).unwrap_or(false);

        if !is_implicit {
            // Look at the type without any implicit arguments
            let mut iter = types::implicit_arg_iter(typ.remove_forall());
            for _ in iter.by_ref() {}
            is_implicit = iter.typ
                .remove_forall()
                .name()
                .and_then(|typename| {
                    self.metadata
                        .get(typename)
                        .or_else(|| self.environment.get_metadata(typename))
                        .and_then(has_implicit_attribute)
                })
                .unwrap_or(false);
        }

        if is_implicit {
            let mut path = path.clone();
            path.push(TypedIdent {
                name: id.clone(),
                typ: typ.clone(),
            });
            consumer(path, typ);
        }
    }

    pub fn make_implicit_ident(&mut self, typ: &ArcType) -> Symbol {
        let name = Symbol::from("implicit_arg");
        let typ = typ.clone();

        let implicits = self.implicit_bindings.last().unwrap().clone();
        debug!(
            "Implicits for {}: {}",
            typ,
            implicits
                .iter()
                .map(|t| format!("{}: {}", t.0.iter().map(|id| &id.name).format("."), t.1))
                .format(",")
        );
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
