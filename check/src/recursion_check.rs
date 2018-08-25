use std::mem;

use base::{
    ast::{self, Expr, Pattern, SpannedExpr, SpannedIdent, Visitor},
    error::Errors,
    pos::{BytePos, Span, Spanned},
    scoped_map::ScopedMap,
    symbol::Symbol,
};

#[derive(Debug, PartialEq, Fail)]
#[fail(display = "`{}` may not be used recursively here", symbol)]
pub struct Error {
    symbol: Symbol,
}

#[derive(Debug, PartialEq)]
enum Context {
    Application,
    Record,
    Lambda,
    Top,
}

#[derive(Debug)]
struct Checker {
    uninitialized_values: ScopedMap<Symbol, ()>,
    context: Context,
    errors: RecursionErrors,
}

pub type RecursionErrors = Errors<Spanned<Error, BytePos>>;

pub fn check_expr(expr: &SpannedExpr<Symbol>) -> Result<(), RecursionErrors> {
    let mut checker = Checker {
        uninitialized_values: ScopedMap::new(),
        context: Context::Top,
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
        match self.context {
            Context::Application | Context::Top if self.uninitialized_values.contains_key(id) => {
                self.errors.push(Spanned {
                    value: Error { symbol: id.clone() },
                    span,
                });
            }
            _ => (),
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

                self.uninitialized_values.extend(
                    bindings
                        .iter()
                        .filter(|bind| bind.args.is_empty())
                        .filter_map(|bind| match bind.name.value {
                            Pattern::Ident(ref id) => Some((id.name.clone(), ())),
                            _ => None,
                        }),
                );

                for bind in bindings {
                    self.visit_expr(&bind.expr);

                    if let Pattern::Ident(ref id) = bind.name.value {
                        self.uninitialized_values.remove(&id.name);
                    }
                }
                self.uninitialized_values.exit_scope();

                self.visit_expr(expr);
            }
            Expr::TypeBindings(_, ref expr) => self.visit_expr(expr),
            Expr::App { .. } => {
                let context = mem::replace(&mut self.context, Context::Application);
                ast::walk_expr(self, expr);
                self.context = context;
            }
            Expr::Lambda(ref lambda) => {
                let uninitialized_values =
                    mem::replace(&mut self.uninitialized_values, Default::default());
                let context = mem::replace(&mut self.context, Context::Lambda);
                self.visit_expr(&lambda.body);
                self.uninitialized_values = uninitialized_values;
                self.context = context;
            }
            Expr::Record { .. } => {
                let context = mem::replace(&mut self.context, Context::Record);
                ast::walk_expr(self, expr);
                self.context = context;
            }
            _ => ast::walk_expr(self, expr),
        }
    }
}
