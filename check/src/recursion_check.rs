//! Checks that the expression do not contain any invalid recursive bindings.
use std::fmt;

use crate::base::{
    ast::{self, Expr, Pattern, SpannedExpr, SpannedIdent, SpannedPattern, TypedIdent, Visitor},
    error::Errors,
    fnv::FnvMap,
    pos::{self, BytePos, Span, Spanned},
    symbol::Symbol,
};

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum Error {
    InvalidRecursion { symbol: Symbol },
    LastExprMustBeConstructor,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InvalidRecursion { symbol } => write!(
                f,
                "`{}` may not be used recursively here",
                symbol.declared_name()
            ),
            Error::LastExprMustBeConstructor => write!(
                f,
                "The last expression a recursive binding must construct a record, a tuple, a variant or a lambda"
            ),
        }
    }
}

type Level = u32;

#[derive(Debug)]
struct Checker {
    /// Symbols that are uninitialized at this point in the program and the level at which they are
    /// defined.
    uninitialized_values: FnvMap<Symbol, Level>,
    /// The current level we are checking.
    level: Level,
    /// Uninitialized symbols that are used in the current expression
    uninitialized_free_variables: Vec<Spanned<Symbol, BytePos>>,
    /// Initialized symbols that are used in the current expression (as long as the function that
    /// contains them do not get called before the symbols are initialized).
    free_variables: Vec<Spanned<Symbol, BytePos>>,
    errors: RecursionErrors,
}

pub type RecursionErrors = Errors<Spanned<Error, BytePos>>;

pub fn check_expr(expr: &SpannedExpr<Symbol>) -> Result<(), RecursionErrors> {
    let mut checker = Checker {
        uninitialized_values: FnvMap::default(),
        level: 0,
        uninitialized_free_variables: Vec::new(),
        free_variables: Vec::new(),
        errors: Errors::new(),
    };
    checker.visit_expr(expr);
    if checker.errors.has_errors() {
        Err(checker.errors)
    } else {
        Ok(())
    }
}

fn is_constructor_expr(expr: &SpannedExpr<Symbol>) -> bool {
    match expr.value {
        Expr::App { ref func, .. } => is_constructor_ident(func),
        _ => false,
    }
}

fn is_constructor_ident(expr: &SpannedExpr<Symbol>) -> bool {
    match expr.value {
        Expr::Ident(ref id) => id.name.declared_name().starts_with(char::is_uppercase),
        _ => false,
    }
}

impl Checker {
    fn check_ident(&mut self, span: Span<BytePos>, id: &Symbol) {
        let uninitialized_status = self.uninitialized_values.get(id);
        if let Some(&id_level) = uninitialized_status {
            if id_level == self.level {
                self.uninitialized_free_variables
                    .push(pos::spanned(span, id.clone()));
            } else {
                // The variable will be initialized when we execute the function at this level
                // however we still need to store the variable so that we know not to call this
                // function before `id`  has been initialized
                self.free_variables.push(pos::spanned(span, id.clone()));
            }
        }
    }

    // A recursive bindings is only allowed if it ends in constructing a value, if it doesn't it is
    // not possible to pre-allocate storage for the value and compile the binding.
    fn check_tail(&mut self, expr: &SpannedExpr<Symbol>) {
        match &expr.value {
            Expr::Block(bs) => self.check_tail(bs.last().unwrap()),
            Expr::LetBindings(_, e) | Expr::TypeBindings(_, e) => {
                self.check_tail(e);
            }
            Expr::IfElse(_, if_true, if_false) => {
                self.check_tail(if_true);
                self.check_tail(if_false);
            }
            Expr::Match(_, alts) => {
                for alt in &**alts {
                    self.check_tail(&alt.expr);
                }
            }
            Expr::Record { .. } | Expr::Tuple { .. } | Expr::Lambda { .. } => (),
            Expr::App { func, .. } => {
                if !is_constructor_ident(func) {
                    self.errors
                        .push(pos::spanned(expr.span, Error::LastExprMustBeConstructor))
                }
            }
            _ => self
                .errors
                .push(pos::spanned(expr.span, Error::LastExprMustBeConstructor)),
        }
    }

    fn taint_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        struct TaintPattern<'a>(&'a mut Checker);
        impl<'a, 'b> Visitor<'a, '_> for TaintPattern<'b> {
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

    fn visit_function_body(&mut self, body: &SpannedExpr<Symbol>) {
        self.level += 1;

        self.visit_expr(body);

        self.level -= 1;

        let uninitialized_free_variables = &mut self.uninitialized_free_variables;
        let uninitialized_values = &self.uninitialized_values;
        let level = self.level;

        self.free_variables.retain(|id| {
            if uninitialized_values.get(&id.value) == Some(&level) {
                uninitialized_free_variables.push(id.clone());
                false
            } else {
                true
            }
        })
    }
}

impl<'a> Visitor<'a, '_> for Checker {
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

                    if bind.args.is_empty() {
                        self.visit_expr(&bind.expr);
                    } else {
                        self.visit_function_body(&bind.expr);
                    }

                    if !self.uninitialized_free_variables[start..].is_empty() {
                        match bind.name.value {
                            Pattern::Ident(ref id) => {
                                if self.uninitialized_free_variables[start..]
                                    .iter()
                                    .any(|used| used.value == id.name)
                                {
                                    // Since the binding itself appeared in this binding we must must
                                    // make sure that the binding can be recursively initialized. This
                                    // is only true if the vm can allocate the binding immediately and
                                    // fill in the values later.
                                    self.check_tail(&bind.expr);
                                }
                            }
                            _ => (),
                        }

                        self.taint_pattern(&bind.name);
                    }
                    if let Pattern::Ident(ref id) = bind.name.value {
                        if self.uninitialized_free_variables[start..]
                            .iter()
                            .all(|var| var.value == id.name)
                        {
                            // The binding is now initialized
                            self.uninitialized_values.remove(&id.name);
                        }
                    }
                }

                self.visit_expr(expr);
            }

            Expr::TypeBindings(_, ref expr) => self.visit_expr(expr),

            Expr::Lambda(ref lambda) => self.visit_function_body(&lambda.body),

            Expr::App { .. } | Expr::Infix { .. } => {
                let start = self.uninitialized_free_variables.len();

                ast::walk_expr(self, expr);

                // Functions may do arbitrary things so don't allow function calls that refer to
                // uninitialized variables
                if !is_constructor_expr(expr) {
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

                // Match expressions may not be done on uninitialized values as they could then
                // view the uninitialized contents
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

                for alt in &**alts {
                    self.visit_expr(&alt.expr);
                }
            }
            _ => ast::walk_expr(self, expr),
        }
    }
}
