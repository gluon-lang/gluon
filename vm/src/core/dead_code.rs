use std::iter::FromIterator;

use petgraph::visit::Walker;

use base::{
    fnv::{FnvMap, FnvSet},
    merge::merge,
    symbol::{Symbol, SymbolRef},
};

use crate::core::{
    self,
    optimize::{walk_expr, walk_expr_alloc, DifferentLifetime, SameLifetime, Visitor},
    Allocator, CExpr, Expr, LetBinding, Named, Pattern,
};

fn is_pure_simple(expr: CExpr) -> bool {
    pub struct SimplePure(bool);

    impl<'l, 'expr> Visitor<'l, 'expr> for SimplePure {
        type Producer = DifferentLifetime<'l, 'expr>;

        fn visit_expr(&mut self, expr: CExpr<'expr>) -> Option<CExpr<'l>> {
            if !self.0 {
                return None;
            }
            match *expr {
                Expr::Call(..) => {
                    self.0 = false;
                    None
                }
                Expr::Let(ref bind, expr) => {
                    match bind.expr {
                        // Creating a group of closures is always pure (though calling them may not be)
                        Named::Recursive(_) => (),
                        Named::Expr(expr) => {
                            self.visit_expr(expr);
                        }
                    }
                    self.visit_expr(expr)
                }
                _ => walk_expr_alloc(self, expr),
            }
        }
        fn detach_allocator(&self) -> Option<&'l Allocator<'l>> {
            None
        }
    }

    let mut visitor = SimplePure(true);
    visitor.visit_expr(expr);
    visitor.0
}

pub fn dead_code_elimination<'a>(allocator: &'a Allocator<'a>, expr: CExpr<'a>) -> CExpr<'a> {
    struct DeadCodeEliminator<'a> {
        allocator: &'a Allocator<'a>,
        used_bindings: FnvSet<&'a SymbolRef>,
    }
    impl DeadCodeEliminator<'_> {
        fn is_used(&self, s: &Symbol) -> bool {
            self.used_bindings.contains(&**s)
        }
    }

    impl<'e> Visitor<'e, 'e> for DeadCodeEliminator<'e> {
        type Producer = SameLifetime<'e>;

        fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
            match expr {
                Expr::Let(bind, body) => {
                    let new_body = self.visit_expr(body);
                    let new_named = match &bind.expr {
                        core::Named::Recursive(closures) => {
                            let used_closures: Vec<_> = closures
                                .iter()
                                .filter(|closure| self.is_used(&closure.name.name))
                                .cloned()
                                .collect();

                            if used_closures.len() == closures.len() {
                                None
                            } else if used_closures.is_empty() {
                                return Some(new_body.unwrap_or(body));
                            } else {
                                Some(core::Named::Recursive(used_closures))
                            }
                        }

                        core::Named::Expr(bind_expr) => {
                            if self.is_used(&bind.name.name) {
                                let new_bind_expr = self.visit_expr(bind_expr);
                                new_bind_expr.map(core::Named::Expr)
                            } else {
                                return Some(new_body.unwrap_or(body));
                            }
                        }
                    };
                    let new_bind = new_named.map(|expr| {
                        &*self.allocator.let_binding_arena.alloc(LetBinding {
                            name: bind.name.clone(),
                            expr,
                            span_start: bind.span_start,
                        })
                    });
                    merge(bind, new_bind, body, new_body, |bind, body| {
                        &*self.allocator.arena.alloc(Expr::Let(bind, body))
                    })
                }

                Expr::Match(scrutinee, alts) if alts.len() == 1 => match &alts[0].pattern {
                    Pattern::Record(fields) => {
                        if !is_pure_simple(scrutinee)
                            || fields
                                .iter()
                                .map(|(x, y)| y.as_ref().unwrap_or(&x.name))
                                .any(|field_bind| self.is_used(&field_bind))
                        {
                            walk_expr_alloc(self, expr)
                        } else {
                            Some(
                                self.visit_expr(alts[0].expr)
                                    .unwrap_or_else(|| alts[0].expr),
                            )
                        }
                    }
                    _ => walk_expr_alloc(self, expr),
                },

                _ => walk_expr_alloc(self, expr),
            }
        }
        fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
            Some(self.allocator)
        }
    }

    let mut free_vars = DeadCodeEliminator {
        allocator,
        used_bindings: DepGraph::default().used_bindings(expr),
    };
    free_vars.visit_expr(expr).unwrap_or(expr)
}

#[derive(Default)]
struct DepGraph<'a> {
    graph: petgraph::Graph<&'a SymbolRef, ()>,
    symbol_map: FnvMap<&'a SymbolRef, petgraph::graph::NodeIndex>,
    currents: Vec<petgraph::graph::NodeIndex>,
}

impl<'a> DepGraph<'a> {
    fn scope(&mut self, id: &'a SymbolRef, f: impl FnOnce(&mut Self)) {
        let Self {
            symbol_map, graph, ..
        } = self;
        let current_idx = *symbol_map.entry(id).or_insert_with(|| graph.add_node(id));
        self.scope_idx(current_idx, f)
    }

    fn scope_idx(&mut self, idx: petgraph::graph::NodeIndex, f: impl FnOnce(&mut Self)) {
        self.currents.push(idx);

        f(self);

        self.currents.pop();
    }

    fn used_bindings<F>(&mut self, expr: CExpr<'a>) -> F
    where
        F: FromIterator<&'a SymbolRef>,
    {
        let top = self.graph.add_node(SymbolRef::new("<top>"));
        self.scope_idx(top, |dep_graph| {
            dep_graph.visit_expr(expr);
        });

        let graph = &self.graph;
        petgraph::visit::Dfs::new(graph, top)
            .iter(graph)
            .flat_map(|idx| graph.node_weight(idx).cloned())
            .collect()
    }
}

impl<'e> Visitor<'e, 'e> for DepGraph<'e> {
    type Producer = SameLifetime<'e>;

    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
        match expr {
            Expr::Ident(id, ..) => {
                let Self {
                    symbol_map,
                    graph,
                    currents,
                    ..
                } = self;

                let current = *currents.last().unwrap();
                let used_id = *symbol_map
                    .entry(&id.name)
                    .or_insert_with(|| graph.add_node(&id.name));
                graph.add_edge(current, used_id, ());

                None
            }
            Expr::Let(bind, body) => {
                match &bind.expr {
                    core::Named::Recursive(closures) => {
                        for closure in closures {
                            self.scope(&closure.name.name, |self_| {
                                self_.visit_expr(closure.expr);
                            });
                        }
                    }
                    core::Named::Expr(bind_expr) => {
                        self.scope(&bind.name.name, |self_| {
                            self_.visit_expr(bind_expr);
                        });
                    }
                }

                self.visit_expr(body)
            }
            _ => {
                walk_expr(self, expr);
                None
            }
        }
    }
    fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::core::optimize::tests::check_optimization;

    #[test]
    fn basic() {
        let initial_str = r#"
            let x = 1
            in
            2
            "#;
        let expected_str = r#"
            2
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn recursive_basic() {
        let initial_str = r#"
            rec let f x = x
            in
            2
            "#;
        let expected_str = r#"
            2
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn eliminate_inner() {
        let initial_str = r#"
            let x =
                let y = ""
                in
                1
            in
            x
            "#;
        let expected_str = r#"
            let x = 1
            in
            x
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn eliminate_redundant_match() {
        let initial_str = r#"
            match { x = 1 } with
            | { x } -> 1
            end
            "#;
        let expected_str = r#"
            1
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn dont_eliminate_used_match() {
        let initial_str = r#"
            rec let f y = y
            in
            let x = f 123
            in
            match { x } with
            | { x } -> x
            end
            "#;
        let expected_str = r#"
            rec let f y = y
            in
            let x = f 123
            in
            match { x } with
            | { x } -> x
            end
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }
}
