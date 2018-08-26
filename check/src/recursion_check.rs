use std::fmt;
use std::mem;

use base::{
    ast::{self, Expr, Pattern, SpannedExpr, SpannedIdent, Visitor},
    error::Errors,
    pos::{BytePos, Span, Spanned},
    scoped_map::ScopedMap,
    symbol::Symbol,
};

#[derive(Debug, PartialEq)]
pub struct Error {
    symbol: Symbol,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "`{}` may not be used recursively here",
            self.symbol.declared_name()
        )
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum Context {
    Eval,
    Lazy,
    Top(usize),
}

impl Context {
    fn replace(&mut self, new_context: Context) -> Context {
        let old = *self;
        if *self != Context::Eval {
            *self = new_context;
        }
        old
    }
}

#[derive(Debug)]
struct Checker {
    uninitialized_values: ScopedMap<Symbol, usize>,
    level: usize,
    uninitialized_free_variables: Vec<Symbol>,
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
        let used_uninitialized_binding = match self.context {
            Context::Eval => self.uninitialized_values.get(id).is_some(),
            Context::Top(level) => self
                .uninitialized_values
                .get(id)
                .map_or(false, |&definition_level| definition_level >= level),
            Context::Lazy => false,
        };
        if used_uninitialized_binding {
            self.errors.push(Spanned {
                value: Error { symbol: id.clone() },
                span,
            });
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

    fn visit_expr(&mut self, expr: &SpannedExpr<Symbol>) {
        match expr.value {
            Expr::Ident(ref id) => self.check_ident(expr.span, &id.name),
            Expr::LetBindings(ref bindings, ref expr) => {
                self.uninitialized_values.enter_scope();
                self.level += 1;

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

                    let uninitialized = &self.uninitialized_free_variables[start..];
                    if uninitialized.is_empty() {
                    } else if let Pattern::Ident(ref id) = bind.name.value {
                        self.uninitialized_values.remove(&id.name);
                    }
                }

                self.level -= 1;
                self.uninitialized_values.exit_scope();

                self.visit_expr(expr);
            }
            Expr::TypeBindings(_, ref expr) => self.visit_expr(expr),
            Expr::App { .. } | Expr::Infix { .. } => {
                let context = self.context.replace(Context::Eval);
                ast::walk_expr(self, expr);
                self.context = context;
            }
            Expr::Lambda(ref lambda) => {
                let uninitialized_values =
                    mem::replace(&mut self.uninitialized_values, Default::default());
                let context = self.context.replace(Context::Lazy);
                self.visit_expr(&lambda.body);
                self.uninitialized_values = uninitialized_values;
                self.context = context;
            }
            Expr::Record { .. } => {
                let context = self.context.replace(Context::Lazy);
                ast::walk_expr(self, expr);
                self.context = context;
            }
            Expr::Match(ref expr, ref alts) => {
                let context = self.context.replace(Context::Eval);
                self.visit_expr(expr);
                self.context = context;

                for alt in alts {
                    self.visit_expr(&alt.expr);
                }
            }
            _ => ast::walk_expr(self, expr),
        }
    }
}
