use base::{
    fnv::{FnvMap, FnvSet},
    symbol::{Symbol, SymbolRef},
};

use crate::core::{
    is_primitive,
    optimize::{walk_expr, SameLifetime, Visitor},
    Allocator, CExpr, Expr, Named,
};

pub type Cost = u32;

#[derive(Clone, Default, Debug)]
pub struct Data {
    pub cost: Cost,
    pub uses: u32,
}

#[derive(Default, Debug)]
pub struct Costs(FnvMap<Symbol, Data>);

impl Costs {
    pub fn cost(&self, s: &SymbolRef) -> Cost {
        self.0.get(s).map_or_else(Cost::max_value, |x| x.cost)
    }

    pub fn uses(&self, s: &SymbolRef) -> u32 {
        self.0.get(s).map_or(0, |x| x.uses)
    }

    pub fn data(&self, s: &SymbolRef) -> Data {
        self.0.get(s).cloned().unwrap_or_default()
    }

    pub fn insert(&mut self, s: Symbol, data: Data) {
        self.0.insert(s, data);
    }
}

struct AnalyzeCost<'a, 'b> {
    cyclic_bindings: &'b FnvSet<&'a SymbolRef>,
    costs: &'b mut Costs,
    bind_stack: FnvSet<&'a SymbolRef>,
    current: Vec<Cost>,
}

impl<'a> AnalyzeCost<'a, '_> {
    fn add_cost(&mut self, cost: Cost) {
        let current_cost = self.current.last_mut().unwrap();
        *current_cost = (*current_cost).saturating_add(cost);
    }

    fn cost_of(&mut self, expr: CExpr<'a>) -> Cost {
        self.current.push(0);
        self.visit_expr(expr);
        self.current.pop().unwrap()
    }

    fn push_bind(&mut self, name: &'a Symbol, expr: CExpr<'a>) -> Cost {
        self.bind_stack.insert(&**name);
        let cost = self
            .cost_of(expr)
            .saturating_add(if self.cyclic_bindings.contains(&**name) {
                Cost::max_value()
            } else {
                0
            });
        self.costs.0.entry(name.clone()).or_default().cost = cost;
        self.bind_stack.remove(&**name);
        cost
    }
}

impl<'a> Visitor<'a, 'a> for AnalyzeCost<'a, '_> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        // The costs here are chosen rather arbitrarily. The only real plan is that at least
        // trivial functions such as `\x y -> x #Int+ y` get inlined
        match *expr {
            Expr::Let(ref bind, body) => {
                match &bind.expr {
                    Named::Recursive(closures) => {
                        for closure in closures {
                            let cost = self.push_bind(&closure.name.name, &closure.expr);
                            self.add_cost(cost);
                        }
                    }
                    Named::Expr(expr) => {
                        let cost = self.push_bind(&bind.name.name, expr);
                        // HACK Add some extra cost since it duplicates the work if we inline a value
                        {
                            let data = self.costs.0.get_mut(&bind.name.name).unwrap();
                            data.cost = data.cost.saturating_add(1000);
                        }
                        self.add_cost(cost);
                    }
                }

                self.visit_expr(body);
            }

            Expr::Match(body, alts) => {
                self.add_cost(5);
                self.visit_expr(body);

                let alt_cost = alts
                    .iter()
                    .map(|alt| self.cost_of(alt.expr))
                    .max()
                    .unwrap_or(0);
                self.add_cost(alt_cost);
            }

            Expr::Call(Expr::Ident(id, ..), ..) if is_primitive(&id.name) => {
                self.add_cost(2);
                walk_expr(self, expr);
            }

            Expr::Call(..) => {
                self.add_cost(5);
                walk_expr(self, expr);
            }

            // Don't inline self recersive functions
            Expr::Ident(ref id, _) if self.bind_stack.contains(&*id.name) => {
                self.costs
                    .0
                    .entry(id.name.clone())
                    .or_insert_with(|| Data {
                        uses: 0,
                        cost: Cost::max_value(),
                    })
                    .uses += 1;
                self.add_cost(Cost::max_value());
            }

            Expr::Ident(ref id, _) => {
                self.costs
                    .0
                    .entry(id.name.clone())
                    .or_insert_with(|| Data {
                        uses: 0,
                        cost: Cost::max_value(),
                    })
                    .uses += 1;
                self.add_cost(1);
            }
            Expr::Const(..) => self.add_cost(1),

            Expr::Data(..) => {
                self.add_cost(5);
                walk_expr(self, expr);
            }

            Expr::Cast(..) => {
                walk_expr(self, expr);
            }
        }
        None
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        None
    }
}

pub(crate) fn analyze_costs<'a>(cyclic_bindings: &FnvSet<&'a SymbolRef>, expr: CExpr<'a>) -> Costs {
    let mut costs = Costs::default();
    let mut visitor = AnalyzeCost {
        cyclic_bindings,
        costs: &mut costs,
        current: vec![0],
        bind_stack: FnvSet::default(),
    };
    visitor.visit_expr(expr);
    costs
}
