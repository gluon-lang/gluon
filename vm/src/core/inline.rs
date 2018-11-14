use base::{
    ast::{Typed, TypedIdent},
    fnv::FnvMap,
    merge::{merge, merge_iter},
    symbol::{Symbol, SymbolRef},
    types::{ArcType, TypeEnv},
};

use crate::core::{
    is_primitive,
    optimize::{walk_expr, walk_expr_alloc, SameLifetime, Visitor},
    Allocator, Binder, CExpr, Closure, Expr, LetBinding, Named,
};

const INLINE_COST_LIMIT: Cost = 20;

pub(crate) struct Inline<'a, 'b> {
    allocator: &'a Allocator<'a>,
    implementations: FnvMap<&'a SymbolRef, (usize, &'a LetBinding<'a>)>,
    env: &'b TypeEnv<Type = ArcType>,
    costs: Costs<'a>,
}

impl<'a, 'b> Inline<'a, 'b> {
    pub fn new(
        allocator: &'a Allocator<'a>,
        env: &'b TypeEnv<Type = ArcType>,
        costs: Costs<'a>,
    ) -> Self {
        Inline {
            allocator,
            implementations: Default::default(), // TODO
            env,
            costs,
        }
    }
}

impl<'a, 'b> Visitor<'a, 'a> for Inline<'a, 'b> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: CExpr<'a>) -> Option<CExpr<'a>> {
        match expr {
            Expr::Call(f, args) => {
                let f = self.visit_expr(f).unwrap_or(f);
                let (closure_id, closure_args, closure_expr) = self.as_closure(f)?;

                if closure_args.len() == args.len() {
                    let closure_cost = self
                        .costs
                        .get(closure_id)
                        .cloned()
                        .unwrap_or_else(usize::max_value);
                    trace!("Inline check of {}: {}", closure_id, closure_cost);

                    if closure_cost < INLINE_COST_LIMIT {
                        let mut binder = Binder::default();

                        let inlined_expr = ReplaceVariables {
                            allocator: self.allocator,
                            ident_replacements: closure_args
                                .iter()
                                .map(|id| &id.name)
                                .zip(args.iter().map(|expr| {
                                    match expr {
                                        Expr::Ident(..) | Expr::Const(..) => expr,
                                        Expr::Data(_, args, _) if args.is_empty() => expr,
                                        _ => &*self
                                            .allocator
                                            .arena
                                            .alloc(binder.bind(expr, expr.env_type_of(self.env))),
                                    }
                                }))
                                .collect(),
                        }
                        .visit_expr(closure_expr)
                        .unwrap_or(closure_expr);

                        Some(binder.into_expr_ref(&self.allocator, inlined_expr))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            Expr::Let(bind, body) => {
                let opt_named = match &bind.expr {
                    Named::Recursive(closures) => merge_iter(
                        closures.iter(),
                        |closure| {
                            self.visit_expr(&closure.expr).map(|closure_expr| Closure {
                                pos: closure.pos.clone(),
                                name: closure.name.clone(),
                                args: closure.args.clone(),
                                expr: closure_expr,
                            })
                        },
                        |closure| closure.clone(),
                    )
                    .map(Named::Recursive),

                    Named::Expr(expr) => {
                        let new_bind = self.visit_expr(expr).map(Named::Expr);

                        new_bind
                    }
                };

                let opt_bind = opt_named.map(|bind_expr| {
                    &*self.allocator.let_binding_arena.alloc(LetBinding {
                        name: bind.name.clone(),
                        expr: bind_expr,
                        span_start: bind.span_start,
                    })
                });

                match &bind.expr {
                    Named::Expr(_) => {
                        self.implementations
                            .insert(&bind.name.name, (0, opt_bind.unwrap_or(&bind)));
                    }

                    Named::Recursive(closures) => {
                        // Only insert the closures after as we do not want to inline the
                        // recursive functions into themselves
                        for (i, closure) in closures.iter().enumerate() {
                            self.implementations.insert(&closure.name.name, (i, &bind));
                        }
                    }
                }

                let opt_body = self.visit_expr(body);

                merge(bind, opt_bind, body, opt_body, |bind, body| {
                    &*self.allocator.arena.alloc(Expr::Let(bind, body))
                })
            }

            _ => walk_expr_alloc(self, expr),
        }
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.allocator)
    }
}

impl<'a, 'b> Inline<'a, 'b> {
    fn get(&self, id: &Symbol) -> Option<(&'a [TypedIdent<Symbol>], CExpr<'a>)> {
        self.implementations
            .get(&**id)
            .map(|&(i, ref bind)| match &bind.expr {
                Named::Recursive(closures) => {
                    let closure = &closures[i];
                    (&*closure.args, closure.expr)
                }
                Named::Expr(expr) => (&[][..], *expr),
            })
    }

    fn as_closure(
        &self,
        expr: CExpr<'a>,
    ) -> Option<(&'a SymbolRef, &'a [TypedIdent<Symbol>], CExpr<'a>)> {
        match expr {
            Expr::Let(
                LetBinding {
                    expr: Named::Recursive(closures),
                    ..
                },
                Expr::Ident(ref id, ..),
            ) => {
                if let Some(closure) = closures.iter().find(|closure| closure.name.name == id.name)
                {
                    Some((&*id.name, &closure.args, &closure.expr))
                } else {
                    None
                }
            }

            Expr::Ident(id, _) => self.get(&id.name).map(|(x, y)| (&*id.name, x, y)),

            _ => None,
        }
    }
}

struct ReplaceVariables<'a> {
    allocator: &'a Allocator<'a>,
    ident_replacements: FnvMap<&'a Symbol, &'a Expr<'a>>,
}

impl<'a> Visitor<'a, 'a> for ReplaceVariables<'a> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        match *expr {
            Expr::Ident(ref id, _) => self.ident_replacements.get(&id.name).cloned(),
            _ => walk_expr_alloc(self, expr),
        }
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.allocator)
    }
}

pub type Cost = usize;
pub type Costs<'a> = FnvMap<&'a SymbolRef, Cost>;

struct AnalyzeCost<'a> {
    costs: Costs<'a>,
    current: Vec<Cost>,
}

impl<'a> AnalyzeCost<'a> {
    fn cost_of(&mut self, expr: CExpr<'a>) -> Cost {
        self.current.push(0);
        self.visit_expr(expr);
        self.current.pop().unwrap()
    }

    fn push_bind(&mut self, name: &'a Symbol, expr: CExpr<'a>) {
        let cost = self.cost_of(expr);
        self.costs.insert(name, cost);
    }
}

impl<'a> Visitor<'a, 'a> for AnalyzeCost<'a> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        // The costs here are chosen rather arbitrarily. The only real plan is that at least
        // trivial functions such as `\x y -> x #Int+ y` get inlined
        match *expr {
            Expr::Let(ref bind, body) => {
                match &bind.expr {
                    Named::Recursive(closures) => {
                        for closure in closures {
                            self.push_bind(&closure.name.name, &closure.expr);
                        }
                    }
                    Named::Expr(expr) => {
                        self.push_bind(&bind.name.name, expr);
                    }
                }

                self.visit_expr(body);
            }

            Expr::Match(body, alts) => {
                *self.current.last_mut().unwrap() += 5;
                self.visit_expr(body);

                *self.current.last_mut().unwrap() += alts
                    .iter()
                    .map(|alt| self.cost_of(alt.expr))
                    .max()
                    .unwrap_or(0)
            }

            Expr::Call(Expr::Ident(id, ..), ..) if is_primitive(&id.name) => {
                *self.current.last_mut().unwrap() += 2;
                walk_expr(self, expr);
            }

            Expr::Call(..) => {
                *self.current.last_mut().unwrap() += 10000;
                walk_expr(self, expr);
            }

            Expr::Const(..) | Expr::Ident(..) => *self.current.last_mut().unwrap() += 1,

            Expr::Data(..) => {
                *self.current.last_mut().unwrap() += 5;
                walk_expr(self, expr);
            }
        }
        None
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        None
    }
}

pub(crate) fn analyze_costs<'a>(expr: CExpr<'a>) -> Costs<'a> {
    let mut visitor = AnalyzeCost {
        costs: FnvMap::default(),
        current: vec![0],
    };
    visitor.visit_expr(expr);
    visitor.costs
}

#[cfg(test)]
mod tests {
    use super::*;

    use base::ast::EmptyEnv;

    use crate::core::tests::check_translation_with;

    fn check_inline(expr_str: &str, expected_str: &str) {
        check_translation_with(expr_str, expected_str, |allocator, expr| {
            let costs = analyze_costs(expr);
            Inline::new(allocator, &EmptyEnv::default(), costs)
                .visit_expr(expr)
                .unwrap_or(expr)
        });
    }

    #[test]
    fn inline_add() {
        let expr_str = r#"
            let add x y = x #Int+ y
            add 1 2
        "#;

        let expected_str = r#"
            rec let add x y = (#Int+) x y
            in
            (#Int+) 1 2
        "#;
        check_inline(expr_str, expected_str);
    }

    #[test]
    fn dont_inline_recursive_function() {
        let expr_str = r#"
            let func x = 1 + func x
            func 1
        "#;

        let expected_str = r#"
            rec let func x = (+) 1 (func x)
            in
            func 1
        "#;
        check_inline(expr_str, expected_str);
    }

    #[test]
    fn inline_through_record() {
        let expr_str = r#"
            let { add } =
                let add x y = x #Int+ y
                { add }
            add 1 2
        "#;

        let expected_str = r#"
            let match_pattern =
                rec let add x y = (#Int+) x y
                in
                { add = add }
            in
            match match_pattern with
            | { add } -> (#Int+) 1 2
            end
        "#;
        check_inline(expr_str, expected_str);
    }
}
