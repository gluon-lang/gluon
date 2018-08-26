use std::fmt;
use std::mem;

use base::{
    ast::{self, Expr, Pattern, SpannedExpr, SpannedIdent, SpannedPattern, TypedIdent, Visitor},
    error::Errors,
    pos::{self, BytePos, Span, Spanned},
    scoped_map::ScopedMap,
    symbol::Symbol,
};

#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidRecursion { symbol: Symbol },
    LastExprMustBeRecord,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InvalidRecursion { symbol } => write!(
                f,
                "`{}` may not be used recursively here",
                symbol.declared_name()
            ),
            Error::LastExprMustBeRecord => write!(
                f,
                "The last expression must be a record in recursive values"
            ),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum Context {
    Lazy,
    Top(usize),
}

impl Context {
    fn replace(&mut self, new_context: Context) -> Context {
        let old = *self;
        *self = new_context;
        old
    }
}

#[derive(Debug)]
struct Checker {
    uninitialized_values: ScopedMap<Symbol, usize>,
    level: usize,
    uninitialized_free_variables: Vec<Spanned<Symbol, BytePos>>,
    context: Context,
    errors: RecursionErrors,
}

pub type RecursionErrors = Errors<Spanned<Error, BytePos>>;

pub fn check_expr(expr: &SpannedExpr<Symbol>) -> Result<(), RecursionErrors> {
    let mut checker = Checker {
        uninitialized_values: ScopedMap::new(),
        level: 0,
        uninitialized_free_variables: Vec::new(),
        context: Context::Top(0),
        errors: Errors::new(),
    };
    checker.visit_expr(expr);
    if checker.errors.has_errors() {
        Err(checker.errors)
    } else {
        Ok(())
    }
}

impl Checker {
    fn check_ident(&mut self, span: Span<BytePos>, id: &Symbol) {
        let uninitialized_status = self.uninitialized_values.get(id);
        if uninitialized_status.is_some() {
            self.uninitialized_free_variables
                .push(pos::spanned(span, id.clone()));
        }
    }

    fn check_tail(&mut self, expr: &SpannedExpr<Symbol>) {
        match expr.value {
            Expr::Block(ref bs) => self.check_tail(bs.last().unwrap()),
            Expr::LetBindings(_, ref e) | Expr::TypeBindings(_, ref e) => {
                self.check_tail(e);
            }
            Expr::IfElse(_, ref if_true, ref if_false) => {
                self.check_tail(if_true);
                self.check_tail(if_false);
            }
            Expr::Match(_, ref alts) => for alt in alts {
                self.check_tail(&alt.expr);
            },
            Expr::Record { .. } | Expr::Tuple { .. } => (),
            _ => self
                .errors
                .push(pos::spanned(expr.span, Error::LastExprMustBeRecord)),
        }
    }
}

impl<'a> Visitor<'a> for Checker {
    type Ident = Symbol;

    fn visit_spanned_typed_ident(&mut self, id: &SpannedIdent<Symbol>) {
        self.check_ident(id.span, &id.value.name);
    }

    fn visit_spanned_ident(&mut self, id: &Spanned<Symbol, BytePos>) {
        self.check_ident(id.span, &id.value);
    }

    fn visit_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        struct TaintPattern<'a>(&'a mut Checker);
        impl<'a, 'b> Visitor<'a> for TaintPattern<'b> {
            type Ident = Symbol;
            fn visit_ident(&mut self, id: &TypedIdent<Symbol>) {
                self.0
                    .uninitialized_values
                    .insert(id.name.clone(), self.0.level);
            }
            fn visit_spanned_ident(&mut self, id: &Spanned<Symbol, BytePos>) {
                self.0
                    .uninitialized_values
                    .insert(id.value.clone(), self.0.level);
            }
        }

        TaintPattern(self).visit_pattern(pattern)
    }

    fn visit_expr(&mut self, expr: &SpannedExpr<Symbol>) {
        match expr.value {
            Expr::Ident(ref id) => self.check_ident(expr.span, &id.name),
            Expr::LetBindings(ref bindings, ref expr) => {
                self.uninitialized_values.enter_scope();
                self.level += 1;
                let context = self.context.replace(Context::Top(self.level));

                let level = self.level;
                self.uninitialized_values.extend(
                    bindings
                        .iter()
                        .filter(|bind| bind.args.is_empty())
                        .filter_map(|bind| match bind.name.value {
                            Pattern::Ident(ref id) => Some((id.name.clone(), level)),
                            _ => None,
                        }),
                );

                for bind in bindings {
                    let start = self.uninitialized_free_variables.len();
                    let context = if !bind.args.is_empty() {
                        self.context.replace(Context::Lazy)
                    } else {
                        self.context
                    };

                    self.visit_expr(&bind.expr);

                    self.context = context;

                    if !self.uninitialized_free_variables[start..].is_empty() {
                        match bind.name.value {
                            Pattern::Ident(ref id) => if self.uninitialized_free_variables[start..]
                                .iter()
                                .any(|used| used.value == id.name)
                            {
                                self.check_tail(&bind.expr);
                            },
                            _ => (),
                        }

                        self.visit_pattern(&bind.name);
                    } else if let Pattern::Ident(ref id) = bind.name.value {
                        self.uninitialized_values.remove(&id.name);
                    }
                }

                self.context = context;
                self.level -= 1;

                self.visit_expr(expr);
            }
            Expr::TypeBindings(_, ref expr) => self.visit_expr(expr),
            Expr::Lambda(ref lambda) => {
                let uninitialized_values =
                    mem::replace(&mut self.uninitialized_values, Default::default());
                let context = self.context.replace(Context::Lazy);
                self.visit_expr(&lambda.body);
                self.uninitialized_values = uninitialized_values;
                self.context = context;
            }
            Expr::App { .. } | Expr::Infix { .. } => {
                let start = self.uninitialized_free_variables.len();

                ast::walk_expr(self, expr);

                {
                    let used_uninitialized_variables = &self.uninitialized_free_variables[start..];
                    self.errors
                        .extend(used_uninitialized_variables.iter().map(|id| Spanned {
                            value: Error::InvalidRecursion {
                                symbol: id.value.clone(),
                            },
                            span: id.span,
                        }));
                }
            }
            Expr::Match(ref expr, ref alts) => {
                let start = self.uninitialized_free_variables.len();
                self.visit_expr(expr);

                {
                    let used_uninitialized_variables = &self.uninitialized_free_variables[start..];
                    self.errors
                        .extend(used_uninitialized_variables.iter().map(|id| Spanned {
                            value: Error::InvalidRecursion {
                                symbol: id.value.clone(),
                            },
                            span: id.span,
                        }));
                }

                for alt in alts {
                    self.visit_expr(&alt.expr);
                }
            }
            _ => ast::walk_expr(self, expr),
        }
    }
}
