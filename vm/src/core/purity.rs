use base::{
    fnv::FnvMap,
    symbol::{Symbol, SymbolRef},
};

use crate::core::{
    optimize::{walk_expr, DifferentLifetime, Visitor},
    Allocator, CExpr, Expr, Named, Pattern,
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum Pureness {
    Call,
    Load,
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
        is_pure: true,
        pure_symbols: &mut pure_symbols,
    };

    visitor.visit_expr(expr);

    pure_symbols
}

struct Pure<'b> {
    is_pure: bool,
    pure_symbols: &'b mut PurityMap,
}

impl Pure<'_> {
    fn is_pure(&mut self, symbol: &Symbol, expr: CExpr) -> bool {
        let mut visitor = Pure {
            is_pure: true,
            pure_symbols: self.pure_symbols,
        };
        visitor.visit_expr(expr);
        let is_pure = visitor.is_pure;
        if is_pure {
            self.pure_symbols.0.insert(symbol.clone(), Pureness::Call);
        }
        is_pure
    }

    fn mark_pure(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Ident(id) => {
                self.pure_symbols.0.insert(id.name.clone(), Pureness::Load);
            }
            Pattern::Record(fields) => {
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
                    if self.pure_symbols.pure_call(&*id.name) || id.name.as_ref().starts_with("#") {
                        walk_expr(self, expr);
                    } else {
                        self.is_pure = false;
                    }
                }
                _ => {
                    self.is_pure = false;
                }
            },

            Expr::Ident(ref id, ..) => {
                if !self.pure_symbols.pure_load(&id.name)
                    && !id.name.as_ref().starts_with("#")
                    && !id.name.is_global()
                {
                    self.is_pure = false;
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
                        self.is_pure &= self.is_pure(&bind.name.name, expr);
                    }
                }
                self.visit_expr(expr);
            }

            Expr::Match(scrutinee, alts) => {
                let is_pure = self.is_pure;

                self.is_pure = true;
                self.visit_expr(scrutinee);
                let scrutinee_is_pure = self.is_pure;

                self.is_pure &= is_pure;

                if scrutinee_is_pure {
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
