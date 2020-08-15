use std::iter::FromIterator;

use petgraph::visit::Walker;

use base::{
    fnv::FnvSet,
    merge::merge,
    scoped_map::ScopedMap,
    symbol::{Symbol, SymbolRef},
};

use crate::core::{
    self,
    optimize::{walk_closures, walk_expr, walk_expr_alloc, SameLifetime, Visitor},
    Allocator, CExpr, Expr, LetBinding, Pattern,
};

pub fn dead_code_elimination<'a>(
    used_bindings: &FnvSet<&'a SymbolRef>,
    allocator: &'a Allocator<'a>,
    expr: CExpr<'a>,
) -> CExpr<'a> {
    trace!("dead_code_elimination: {}", expr);
    struct DeadCodeEliminator<'a, 'b> {
        allocator: &'a Allocator<'a>,
        used_bindings: &'b FnvSet<&'a SymbolRef>,
    }
    impl DeadCodeEliminator<'_, '_> {
        fn is_used(&self, s: &Symbol) -> bool {
            self.used_bindings.contains(&**s)
        }
    }

    impl<'e> Visitor<'e, 'e> for DeadCodeEliminator<'e, '_> {
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

                            walk_closures(self, &used_closures)
                                .or_else(|| {
                                    if used_closures.len() == closures.len() {
                                        None
                                    } else {
                                        Some(used_closures)
                                    }
                                })
                                .map(core::Named::Recursive)
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
                        match &bind.expr {
                            core::Named::Recursive(closures) if closures.is_empty() => body,
                            _ => &*self.allocator.arena.alloc(Expr::Let(bind, body)),
                        }
                    })
                }

                Expr::Match(_, alts) if alts.len() == 1 => match &alts[0].pattern {
                    Pattern::Record { fields, .. } => {
                        if fields
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
        used_bindings,
    };
    free_vars.visit_expr(expr).unwrap_or(expr)
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum Scope<'a> {
    Symbol(&'a SymbolRef),
    Match(usize),
}

#[derive(Default)]
pub struct DepGraph<'a> {
    graph: petgraph::Graph<Scope<'a>, ()>,
    symbol_map: ScopedMap<Scope<'a>, petgraph::graph::NodeIndex>,
    currents: Vec<(BindType, petgraph::graph::NodeIndex)>,
    match_id: usize,
}

static TOP: &str = "<top>";

#[derive(PartialEq)]
enum BindType {
    Closure,
    Expr,
}

impl<'a> DepGraph<'a> {
    fn scope(&mut self, id: &'a SymbolRef, bind_type: BindType, f: impl FnOnce(&mut Self)) {
        let current_idx = self.add_node(Scope::Symbol(id));
        self.scope_idx(current_idx, bind_type, f)
    }

    fn scope_idx(
        &mut self,
        idx: petgraph::graph::NodeIndex,
        bind_type: BindType,
        f: impl FnOnce(&mut Self),
    ) {
        self.currents.push((bind_type, idx));

        f(self);

        self.currents.pop();
    }

    fn add_node(&mut self, scope: Scope<'a>) -> petgraph::graph::NodeIndex {
        let Self {
            symbol_map, graph, ..
        } = self;
        *symbol_map
            .entry(scope)
            .or_insert_with(|| graph.add_node(scope))
    }

    fn bind_pattern(&mut self, pattern: &'a Pattern, scrutinee_id: petgraph::graph::NodeIndex) {
        match pattern {
            Pattern::Ident(ref id) => {
                let id_id = self.add_node(Scope::Symbol(&id.name));
                self.graph.add_edge(id_id, scrutinee_id, ());
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let name = field.1.as_ref().unwrap_or(&field.0.name);
                    let id_id = self.add_node(Scope::Symbol(name));
                    self.graph.add_edge(id_id, scrutinee_id, ());
                }
            }
            Pattern::Constructor(_, fields) => {
                for field in fields {
                    let id_id = self.add_node(Scope::Symbol(&field.name));
                    self.graph.add_edge(id_id, scrutinee_id, ());
                }
            }
            Pattern::Literal(_) => (),
        }
    }

    pub fn cycles<'s>(
        &'s self,
    ) -> impl Iterator<Item = impl Iterator<Item = &'a SymbolRef> + 's> + 's {
        petgraph::algo::tarjan_scc(&self.graph)
            .into_iter()
            .filter_map(move |cycle| {
                if cycle.len() == 1 {
                    let node = cycle[0];
                    if self.graph.find_edge(node, node).is_some() {
                        Some(itertools::Either::Left(
                            self.graph.node_weight(node).cloned().into_iter(),
                        ))
                    } else {
                        None
                    }
                } else {
                    Some(itertools::Either::Right(
                        cycle
                            .into_iter()
                            .flat_map(move |node| self.graph.node_weight(node).cloned()),
                    ))
                }
            })
            .map(|iter| {
                iter.filter_map(|scope| match scope {
                    Scope::Symbol(s) => Some(s),
                    Scope::Match(_) => None,
                })
            })
    }

    pub fn used_bindings<F>(&mut self, expr: CExpr<'a>) -> F
    where
        F: FromIterator<&'a SymbolRef>,
    {
        let top_symbol = SymbolRef::new(TOP);
        let top = self.graph.add_node(Scope::Symbol(top_symbol));
        self.symbol_map.insert(Scope::Symbol(top_symbol), top);

        self.scope_idx(top, BindType::Expr, |dep_graph| {
            dep_graph.visit_expr(expr);
        });

        trace!("DepGraph: {:?}", petgraph::dot::Dot::new(&self.graph));

        let graph = &self.graph;
        petgraph::visit::Dfs::new(graph, top)
            .iter(graph)
            .flat_map(|idx| {
                graph.node_weight(idx).and_then(|scope| match *scope {
                    Scope::Symbol(s) => Some(s),
                    Scope::Match(_) => None,
                })
            })
            .collect()
    }
}

impl<'e> Visitor<'e, 'e> for DepGraph<'e> {
    type Producer = SameLifetime<'e>;

    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
        match expr {
            Expr::Ident(id, ..) => {
                let current = self.currents.last().unwrap().1;
                let used_id = self.add_node(Scope::Symbol(&id.name));
                self.graph.add_edge(current, used_id, ());

                None
            }

            Expr::Call(Expr::Ident(id, ..), ..) if !id.name.as_str().starts_with('#') => {
                for window in self
                    .currents
                    .windows(2)
                    .rev()
                    .take_while(|t| t[1].0 == BindType::Expr)
                {
                    self.graph.add_edge(window[0].1, window[1].1, ());
                }
                walk_expr(self, expr);
                None
            }

            Expr::Let(bind, body) => {
                self.symbol_map.enter_scope();

                match &bind.expr {
                    core::Named::Recursive(closures) => {
                        for closure in closures {
                            let id = &closure.name.name;
                            self.add_node(Scope::Symbol(id));
                        }

                        for closure in closures {
                            self.scope(&closure.name.name, BindType::Closure, |self_| {
                                self_.visit_expr(closure.expr);
                            });
                        }
                    }
                    core::Named::Expr(bind_expr) => {
                        self.scope(&bind.name.name, BindType::Expr, |self_| {
                            self_.visit_expr(bind_expr);
                        });
                    }
                }

                self.visit_expr(body);

                self.symbol_map.exit_scope();

                None
            }

            Expr::Match(scrutinee, alts) => {
                let id = Scope::Match(self.match_id);
                self.match_id += 1;
                let scrutinee_id = self.graph.add_node(id);

                for alt in *alts {
                    self.bind_pattern(&alt.pattern, scrutinee_id);
                }

                self.scope_idx(scrutinee_id, BindType::Expr, |self_| {
                    self_.visit_expr(scrutinee);
                });

                if alts.iter().any(|alt| match alt.pattern {
                    Pattern::Constructor(..) | Pattern::Literal(..) => true,
                    _ => false,
                }) {
                    let current = self.currents.last().unwrap().1;
                    self.graph.add_edge(current, scrutinee_id, ());
                }

                for alt in *alts {
                    self.visit_expr(&alt.expr);
                }

                None
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

    use base::symbol::Symbols;

    use crate::core::optimize::tests::check_optimization;

    fn dead_code_elimination<'a>(allocator: &'a Allocator<'a>, expr: CExpr<'a>) -> CExpr<'a> {
        let mut dep_graph = crate::core::dead_code::DepGraph::default();
        let used_bindings = dep_graph.used_bindings(expr);

        super::dead_code_elimination(&used_bindings, allocator, expr)
    }

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
    fn eliminate_let_used_in_redundant_match() {
        let initial_str = r#"
            let a = 1 in
            match { x = a } with
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

    #[test]
    fn dont_eliminate_let_in_constructor_match() {
        let initial_str = r#"
            let y = 1 in
            match y with
            | LT -> 1
            end
            "#;
        let expected_str = r#"
            let y = 1 in
            match y with
            | LT -> 1
            end
            "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn dont_eliminate_constructor_with_used_binding() {
        let initial_str = r#"
            rec let f y =
                match y with
                | Test a ->
                    match a with
                    | 1 -> 1
                    | _ -> 2
                    end
                end
            in f
            "#;
        let expected_str = r#"
            rec let f y =
                match y with
                | Test a ->
                    match a with
                    | 1 -> 1
                    | _ -> 2
                    end
                end
            in f
           "#;
        check_optimization(initial_str, expected_str, dead_code_elimination);
    }

    #[test]
    fn cycles() {
        let expr_str = r#"
            let z = 1
            in

            rec let f y1 =
                let a = z in
                g y1 z
            rec let g y2 = f y2
            in

            rec let h y3 = h y3
            in

            let a = g y
            in 1
            "#;

        let mut symbols = Symbols::new();
        let allocator = Allocator::new();
        let expr = crate::core::interpreter::tests::parse_expr(&mut symbols, &allocator, expr_str);

        let mut dep_graph = DepGraph::default();
        dep_graph.visit_expr(expr);
        assert_eq!(
            dep_graph
                .cycles()
                .map(|group| group.map(|s| s.to_string()).collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![
                vec!["g".to_string(), "f".to_string()],
                vec!["h".to_string()]
            ],
            "{:?}",
            petgraph::dot::Dot::new(&dep_graph.graph)
        );
    }
}
