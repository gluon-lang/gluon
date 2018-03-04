use itertools::Itertools;

use base::ast::{self, Expr, MutVisitor, SpannedExpr, TypedIdent};
use base::types::{self, ArcType};
use base::pos::{self, BytePos, Span, Spanned};
use base::scoped_map::ScopedMap;
use base::symbol::Symbol;

use typecheck::{ImplictBindings, TcResult, TypeError, Typecheck};

const MAX_IMPLICIT_LEVEL: u32 = 20;

struct ResolveImplicitsVisitor<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
}

impl<'a, 'b> ResolveImplicitsVisitor<'a, 'b> {
    fn resolve_implicit_application(
        &mut self,
        level: u32,
        implicit_bindings: &ImplictBindings,
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
        implicit_bindings: &ImplictBindings,
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
                    let found_candidate = implicit_bindings.iter().rev().find(|&&(_, ref typ)| {
                        self.try_implicit(&mut to_resolve, expected_type, typ)
                    });
                    match found_candidate {
                        Some(&(ref path, _)) => {
                            debug!("Success! Resolving arguments");
                            match self.resolve_implicit_application(
                                level + 1,
                                implicit_bindings,
                                span,
                                path,
                                &to_resolve,
                            ) {
                                Ok(opt) => opt.map(Ok),
                                Err(err) => Some(Err(err)),
                            }
                        }
                        None => None,
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
        to_resolve: &mut Vec<ArcType>,
        expected_type: &ArcType,
        typ: &ArcType,
    ) -> bool {
        debug!("Trying implicit {}", typ);
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
}

impl<'a, 'b> MutVisitor for ResolveImplicitsVisitor<'a, 'b> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
        let mut replacement = None;
        if let Expr::Ident(ref mut id) = expr.value {
            if let Some(implicit_bindings) = self.tc.implicit_vars.get(&id.name).cloned() {
                debug!(
                    "Resolving {} against:\n{}",
                    id.typ,
                    implicit_bindings.iter().map(|t| &t.1).format("\n")
                );
                let span = expr.span;
                let mut to_resolve = Vec::new();
                let found_candidate = implicit_bindings
                    .iter()
                    .rev()
                    .find(|&&(_, ref typ)| self.try_implicit(&mut to_resolve, &id.typ, typ));
                let resolution_result = found_candidate.and_then(|&(ref path, _)| {
                    debug!(
                        "Found implicit candidate `{}`. Trying its implicit arguments (if any)",
                        path.iter().rev().map(|id| &id.name).format(".")
                    );
                    match self.resolve_implicit_application(
                        0,
                        &implicit_bindings,
                        span,
                        &path,
                        &to_resolve,
                    ) {
                        Ok(opt) => opt.map(Ok),
                        Err(err) => Some(Err(err)),
                    }
                });
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
                                        path.iter().map(|id| &id.name).format(".").to_string()
                                    })
                                    .collect(),
                            ).into(),
                        });
                        None
                    }
                };
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

pub fn resolve(tc: &mut Typecheck, expr: &mut SpannedExpr<Symbol>) {
    let mut visitor = ResolveImplicitsVisitor { tc };
    visitor.visit_expr(expr);
}
