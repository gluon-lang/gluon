use base::{
    fnv::FnvMap,
    symbol::{Symbol, SymbolRef},
};

use crate::core::{
    optimize::{walk_expr, DifferentLifetime, Visitor},
    Allocator, CExpr, Expr, Named, Pattern,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Pureness {
    None,
    Load,
    Call,
}

impl Pureness {
    fn merge(&mut self, pureness: Pureness) {
        *self = (*self).min(pureness);
    }
}

#[derive(Clone, Default, Debug)]
pub struct PurityMap(FnvMap<Symbol, Pureness>);

impl PurityMap {
    pub fn pure_call(&self, k: &SymbolRef) -> bool {
        self.0.get(k).map_or(false, |p| *p == Pureness::Call)
    }

    pub fn pure_load(&self, k: &SymbolRef) -> bool {
        self.0.contains_key(k)
    }
}

pub fn purity<'a>(expr: CExpr<'a>) -> PurityMap {
    let mut pure_symbols = PurityMap(FnvMap::default());

    let mut visitor = Pure {
        is_pure: Pureness::Call,
        pure_symbols: &mut pure_symbols,
    };

    visitor.visit_expr(expr);

    pure_symbols
}

struct Pure<'b> {
    is_pure: Pureness,
    pure_symbols: &'b mut PurityMap,
}

impl Pure<'_> {
    fn is_pure(&mut self, symbol: &Symbol, expr: CExpr) -> Pureness {
        let mut visitor = Pure {
            is_pure: Pureness::Call,
            pure_symbols: self.pure_symbols,
        };
        visitor.visit_expr(expr);
        let is_pure = visitor.is_pure;
        if is_pure != Pureness::None {
            self.pure_symbols.0.insert(symbol.clone(), is_pure);
        }
        is_pure
    }

    fn mark_pure(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Ident(id) => {
                self.pure_symbols.0.insert(id.name.clone(), Pureness::Load);
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    self.pure_symbols.0.insert(
                        field.1.as_ref().unwrap_or(&field.0.name).clone(),
                        Pureness::Load,
                    );
                }
            }
            Pattern::Constructor(_, params) => {
                for param in params {
                    self.pure_symbols
                        .0
                        .insert(param.name.clone(), Pureness::Load);
                }
            }
            Pattern::Literal(_) => (),
        }
    }
}

impl<'l, 'expr> Visitor<'l, 'expr> for Pure<'_> {
    type Producer = DifferentLifetime<'l, 'expr>;

    fn visit_expr(&mut self, expr: CExpr<'expr>) -> Option<CExpr<'l>> {
        match *expr {
            Expr::Call(ref f, _) => match f {
                Expr::Ident(ref id, ..) => {
                    if self.pure_symbols.pure_call(&*id.name) || id.name.is_primitive() {
                        walk_expr(self, expr);
                    } else {
                        self.is_pure = Pureness::None;
                    }
                }
                _ => {
                    self.is_pure = Pureness::None;
                }
            },

            Expr::Ident(ref id, ..) => {
                if !self.pure_symbols.pure_load(&id.name)
                    && !id.name.is_primitive()
                    && !id.name.is_global()
                {
                    self.is_pure.merge(Pureness::Load);
                }
            }

            Expr::Let(ref bind, expr) => {
                match bind.expr {
                    // Creating a group of closures is always pure (though calling them may not be)
                    Named::Recursive(ref closures) => {
                        for closure in closures {
                            for arg in &closure.args {
                                self.pure_symbols.0.insert(arg.name.clone(), Pureness::Load);
                            }
                            self.is_pure(&closure.name.name, closure.expr);
                        }
                    }
                    Named::Expr(expr) => {
                        let is_pure = self.is_pure(&bind.name.name, expr);
                        self.is_pure.merge(is_pure);
                    }
                }
                self.visit_expr(expr);
            }

            Expr::Match(scrutinee, alts) => {
                let is_pure = self.is_pure;

                self.is_pure = Pureness::Call;
                self.visit_expr(scrutinee);
                let scrutinee_is_pure = self.is_pure;

                self.is_pure.merge(is_pure);

                if scrutinee_is_pure != Pureness::None {
                    for alt in alts {
                        self.mark_pure(&alt.pattern);
                    }
                }
                for alt in alts {
                    self.visit_expr(alt.expr);
                }
            }

            _ => {
                walk_expr(self, expr);
            }
        }
        None
    }
    fn detach_allocator(&self) -> Option<&'l Allocator<'l>> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::Arc;

    use base::symbol::Symbols;

    use crate::core::interpreter::tests::parse_expr;

    #[test]
    fn pure_global() {
        let mut symbols = Symbols::new();

        let allocator = Arc::new(Allocator::new());

        let expr = parse_expr(&mut symbols, &allocator, "let x = global in x");

        assert_eq!(
            purity(expr).0,
            collect![(symbols.simple_symbol("x"), Pureness::Load)]
        );
    }
}
