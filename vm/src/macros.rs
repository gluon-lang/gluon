//! Module providing the building blocks to create macros and expand them.
use std::any::Any;
use std::error::Error as StdError;
use std::mem;
use std::sync::{Arc, RwLock};

use futures::{stream, Future, Stream};

use base::ast::{self, Expr, MutVisitor, SpannedExpr};
use base::error::Errors as BaseErrors;
use base::fnv::FnvMap;
use base::pos;
use base::pos::{BytePos, Spanned};
use base::symbol::{Symbol, Symbols};

use thread::Thread;

pub type Error = Box<StdError + Send + Sync>;
pub type SpannedError = Spanned<Error, BytePos>;
pub type Errors = BaseErrors<SpannedError>;
pub type MacroFuture = Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send>;

/// A trait which abstracts over macros.
///
/// A macro is similiar to a function call but is run at compile time instead of at runtime.
pub trait Macro: ::mopa::Any + Send + Sync {
    fn expand(&self, env: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture;
}

mopafy!(Macro);

impl<F: ::mopa::Any + Clone + Send + Sync> Macro for F
where
    F: Fn(&mut MacroExpander, Vec<SpannedExpr<Symbol>>)
        -> Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send>,
{
    fn expand(
        &self,
        env: &mut MacroExpander,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> Box<Future<Item = SpannedExpr<Symbol>, Error = Error> + Send> {
        self(env, args)
    }
}

/// Type containing macros bound to symbols which can be applied on an AST expression to transform
/// it.
#[derive(Default)]
pub struct MacroEnv {
    macros: RwLock<FnvMap<String, Arc<Macro>>>,
}

impl MacroEnv {
    /// Creates a new `MacroEnv`
    pub fn new() -> MacroEnv {
        MacroEnv {
            macros: RwLock::new(FnvMap::default()),
        }
    }

    /// Inserts a `Macro` which acts on any occurance of `symbol` when applied to an expression.
    pub fn insert<M>(&self, name: String, mac: M)
    where
        M: Macro + 'static,
    {
        self.macros.write().unwrap().insert(name, Arc::new(mac));
    }

    /// Retrieves the macro bound to `symbol`
    pub fn get(&self, name: &str) -> Option<Arc<Macro>> {
        self.macros.read().unwrap().get(name).cloned()
    }

    /// Runs the macros in this `MacroEnv` on `expr` using `env` as the context of the expansion
    pub fn run(
        &self,
        vm: &Thread,
        symbols: &mut Symbols,
        expr: &mut SpannedExpr<Symbol>,
    ) -> Result<(), Errors> {
        let mut expander = MacroExpander::new(vm);
        expander.run(symbols, expr);
        expander.finish()
    }
}

pub struct MacroExpander<'a> {
    pub state: FnvMap<String, Box<Any>>,
    pub vm: &'a Thread,
    pub errors: Errors,
    pub error_in_expr: bool,
    macros: &'a MacroEnv,
}

impl<'a> MacroExpander<'a> {
    pub fn new(vm: &'a Thread) -> MacroExpander<'a> {
        MacroExpander {
            vm: vm,

            state: FnvMap::default(),
            macros: vm.get_macros(),
            error_in_expr: false,
            errors: Errors::new(),
        }
    }

    pub fn finish(self) -> Result<(), Errors> {
        if self.error_in_expr || self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }

    pub fn run(&mut self, symbols: &mut Symbols, expr: &mut SpannedExpr<Symbol>) {
        {
            let exprs = {
                let mut visitor = MacroVisitor {
                    expander: self,
                    symbols,
                    exprs: Vec::new(),
                };
                visitor.visit_expr(expr);
                visitor.exprs
            };
            let _ = stream::futures_ordered(exprs.into_iter().map(move |(expr, future)| {
                future.then(move |result| -> Result<_, ()> {
                    match result {
                        Ok(mut replacement) => {
                            replacement.span = expr.span;
                            replace_expr(expr, replacement);
                            Ok(None)
                        }
                        Err(err) => {
                            let expr_span = expr.span;
                            replace_expr(expr, pos::spanned(expr_span, Expr::Error(None)));

                            Ok(Some(pos::spanned(expr.span, err)))
                        }
                    }
                })
            })).for_each(|err| -> Result<(), ()> {
                if let Some(err) = err {
                    self.errors.push(err);
                }
                Ok(())
            })
                .wait();
        }
        if self.errors.has_errors() {
            info!("Macro errors: {}", self.errors);
        }
    }
}

fn replace_expr(expr: &mut SpannedExpr<Symbol>, new: SpannedExpr<Symbol>) {
    let expr_span = expr.span;
    let original = mem::replace(expr, pos::spanned(expr_span, Expr::Error(None)));
    *expr = pos::spanned(
        expr.span,
        Expr::MacroExpansion {
            original: Box::new(original),
            replacement: Box::new(new),
        },
    );
}

struct MacroVisitor<'a: 'b, 'b, 'c> {
    expander: &'b mut MacroExpander<'a>,
    symbols: &'c mut Symbols,
    exprs: Vec<(&'c mut SpannedExpr<Symbol>, MacroFuture)>,
}

impl<'a, 'b, 'c> MutVisitor<'c> for MacroVisitor<'a, 'b, 'c> {
    type Ident = Symbol;

    fn visit_expr(&mut self, expr: &'c mut SpannedExpr<Symbol>) {
        let replacement = match expr.value {
            Expr::App {
                ref mut implicit_args,
                func: ref mut id,
                ref mut args,
            } => match id.value {
                Expr::Ident(ref id) if id.name.as_ref().ends_with('!') => {
                    if !implicit_args.is_empty() {
                        self.expander.errors.push(pos::spanned(
                            expr.span,
                            "Implicit arguments are not allowed on macros".into(),
                        ));
                    }

                    let name = id.name.as_ref();
                    match self.expander.macros.get(&name[..name.len() - 1]) {
                        // FIXME Avoid cloning args
                        Some(m) => Some(m.expand(self.expander, args.clone())),
                        None => None,
                    }
                }
                _ => None,
            },
            Expr::TypeBindings(ref binds, ref mut body) => {
                for bind in binds {
                    if let Some(derive) = bind
                        .metadata
                        .attributes
                        .iter()
                        .find(|attr| attr.name == "derive")
                    {
                        match derive.arguments {
                            Some(ref args) => for arg in args.split(',').map(|s| s.trim()) {
                                let result = match arg {
                                    "Eq" => generate_eq(self.symbols, bind),
                                    "Show" => generate_show(self.symbols, bind),
                                    _ => panic!(),
                                };
                                let generated_binding = match result {
                                    Ok(x) => x,
                                    Err(err) => {
                                        self.expander
                                            .errors
                                            .push(pos::spanned(bind.name.span, err));
                                        continue;
                                    }
                                };
                                let next_expr = mem::replace(body, Default::default());

                                **body = pos::spanned(
                                    Default::default(),
                                    Expr::LetBindings(vec![generated_binding], next_expr),
                                );
                            },
                            _ => {
                                self.expander.errors.push(pos::spanned(
                                    bind.name.span,
                                    "Invalid `derive` attribute".into(),
                                ));
                                continue;
                            }
                        }
                    }
                }
                None
            }
            _ => None,
        };
        if let Some(future) = replacement {
            self.exprs.push((expr, future));
        } else {
            ast::walk_mut_expr(self, expr);
        }
    }
}

use base::ast::{
    Alternative, Argument, ExprField, Literal, Pattern, PatternField, TypeBinding, TypedIdent,
    ValueBinding,
};
use base::pos::Span;
use base::types::{arg_iter, row_iter, Type};

fn ident(span: Span<BytePos>, s: Symbol) -> SpannedExpr<Symbol> {
    pos::spanned(span, Expr::Ident(TypedIdent::new(s)))
}

fn literal(span: Span<BytePos>, s: &str) -> SpannedExpr<Symbol> {
    pos::spanned(span, Expr::Literal(Literal::String(s.to_string())))
}

fn app(span: Span<BytePos>, func: Symbol, args: Vec<SpannedExpr<Symbol>>) -> SpannedExpr<Symbol> {
    pos::spanned(
        Default::default(),
        Expr::App {
            func: Box::new(pos::spanned(span, Expr::Ident(TypedIdent::new(func)))),
            implicit_args: Vec::new(),
            args,
        },
    )
}

fn infix(
    span: Span<BytePos>,
    lhs: SpannedExpr<Symbol>,
    op: Symbol,
    rhs: SpannedExpr<Symbol>,
) -> SpannedExpr<Symbol> {
    pos::spanned(
        Default::default(),
        Expr::Infix {
            lhs: lhs.into(),
            op: pos::spanned(span, TypedIdent::new(op)),
            rhs: rhs.into(),
            implicit_args: Vec::new(),
        },
    )
}

fn generate_show(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let x = Symbol::from("x");

    let show_expr = match **bind.alias.value.unresolved_type() {
        Type::Variant(ref variants) => {
            let alts = row_iter(variants)
                .map(|variant| {
                    let pattern_args: Vec<_> = arg_iter(&variant.typ)
                        .enumerate()
                        .map(|(i, _)| TypedIdent::new(Symbol::from(format!("arg_{}", i))))
                        .collect();

                    let expr = {
                        let open_brace = literal(span, variant.name.declared_name());

                        pattern_args.iter().fold(open_brace, |acc, x| {
                            let show = infix(
                                span,
                                literal(span, "("),
                                symbols.symbol("++"),
                                infix(
                                    span,
                                    app(
                                        span,
                                        symbols.symbol("show"),
                                        vec![ident(span, x.name.clone())],
                                    ),
                                    symbols.symbol("++"),
                                    literal(span, ")"),
                                ),
                            );
                            infix(
                                span,
                                acc,
                                symbols.symbol("++"),
                                infix(span, literal(span, " "), symbols.symbol("++"), show),
                            )
                        })
                    };

                    let ctor_pattern = |pattern_args: Vec<_>| {
                        pos::spanned(
                            span,
                            Pattern::Constructor(
                                TypedIdent::new(variant.name.clone()),
                                pattern_args
                                    .into_iter()
                                    .map(|arg| pos::spanned(span, Pattern::Ident(arg)))
                                    .collect(),
                            ),
                        )
                    };
                    Alternative {
                        pattern: ctor_pattern(pattern_args),
                        expr,
                    }
                })
                .collect();
            Expr::Match(Box::new(ident(span, x.clone())), alts)
        }
        Type::Record(ref row) => {
            let field_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}", field.name.declared_name())))
                })
                .collect();

            let expr = {
                let open_brace = literal(span, "{ ");

                let show_expr = field_symbols
                    .iter()
                    .enumerate()
                    .fold(open_brace, |acc, (i, x)| {
                        let show = app(
                            span,
                            symbols.symbol("show"),
                            vec![ident(span, x.name.clone())],
                        );

                        let show_field = infix(
                            span,
                            acc,
                            symbols.symbol("++"),
                            infix(
                                span,
                                literal(span, &format!("{} = ", x.name.declared_name())),
                                symbols.symbol("++"),
                                show,
                            ),
                        );

                        let last = i == field_symbols.len() - 1;
                        let suffix = if last { " " } else { ", " };
                        infix(
                            span,
                            show_field,
                            symbols.symbol("++"),
                            literal(span, suffix),
                        )
                    });

                infix(span, show_expr, symbols.symbol("++"), literal(span, "}"))
            };
            let generate_record_pattern = |symbols| {
                pos::spanned(
                    span,
                    Pattern::Record {
                        implicit_import: None,
                        typ: Type::hole(),
                        types: Vec::new(),
                        fields: row_iter(row)
                            .zip(symbols)
                            .map(|(field, bind)| PatternField {
                                name: pos::spanned(span, field.name.clone()),
                                value: Some(pos::spanned(span, Pattern::Ident(bind))),
                            })
                            .collect(),
                    },
                )
            };
            Expr::Match(
                Box::new(ident(span, x.clone())),
                vec![Alternative {
                    pattern: generate_record_pattern(field_symbols),
                    expr,
                }],
            )
        }
        _ => return Err("Unable to derive Show for this type".into()),
    };

    let show_fn = TypedIdent::new(symbols.symbol("show_"));
    let show_record_expr = Expr::LetBindings(
        vec![ValueBinding {
            name: pos::spanned(span, Pattern::Ident(show_fn.clone())),
            args: vec![Argument::explicit(pos::spanned(
                span,
                TypedIdent::new(x.clone()),
            ))],
            expr: pos::spanned(span, show_expr),
            metadata: Default::default(),
            typ: Some(Type::function(
                vec![Type::ident(bind.alias.value.name.clone())],
                Type::string(),
            )),
            resolved_type: Type::hole(),
        }],
        Box::new(pos::spanned(
            span,
            Expr::Record {
                typ: Type::hole(),
                types: Vec::new(),
                exprs: vec![ExprField {
                    metadata: Default::default(),
                    name: pos::spanned(span, symbols.symbol("show")),
                    value: Some(ident(span, show_fn.name.clone())),
                }],
                base: None,
            },
        )),
    );
    Ok(ValueBinding {
        name: pos::spanned(span, Pattern::Ident(TypedIdent::new(Symbol::from("show")))),
        args: Vec::new(),
        expr: pos::spanned(span, show_record_expr),
        metadata: Default::default(),
        typ: Some(Type::app(
            Type::ident(symbols.symbol("Show")),
            collect![Type::ident(bind.alias.value.name.clone())],
        )),
        resolved_type: Type::hole(),
    })
}

fn generate_eq(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let l = Symbol::from("l");
    let r = Symbol::from("r");
    let matcher = Box::new(pos::spanned(
        span,
        Expr::Tuple {
            typ: Type::hole(),
            elems: vec![ident(span, l.clone()), ident(span, r.clone())],
        },
    ));

    let generate_and_chain =
        |symbols: &mut Symbols,
         iter: &mut Iterator<Item = (&TypedIdent<Symbol>, &TypedIdent<Symbol>)>| {
            let true_expr = ident(span, symbols.symbol("True"));
            iter.fold(true_expr, |acc, (l, r)| {
                infix(
                    span,
                    acc,
                    symbols.symbol("&&"),
                    infix(
                        span,
                        ident(span, l.name.clone()).into(),
                        symbols.symbol("=="),
                        ident(span, r.name.clone()),
                    ),
                )
            })
        };

    let comparison_expr = match **bind.alias.value.unresolved_type() {
        Type::Variant(ref variants) => {
            let alts = row_iter(variants)
                .map(|variant| {
                    let l_pattern_args: Vec<_> = arg_iter(&variant.typ)
                        .map(|_| TypedIdent::new(Symbol::from("arg_l")))
                        .collect();
                    let r_pattern_args: Vec<_> = arg_iter(&variant.typ)
                        .map(|_| TypedIdent::new(Symbol::from("arg_r")))
                        .collect();

                    let expr = generate_and_chain(
                        symbols,
                        &mut l_pattern_args.iter().zip(&r_pattern_args),
                    );

                    let ctor_pattern = |pattern_args: Vec<_>| {
                        pos::spanned(
                            span,
                            Pattern::Constructor(
                                TypedIdent::new(variant.name.clone()),
                                pattern_args
                                    .into_iter()
                                    .map(|arg| pos::spanned(span, Pattern::Ident(arg)))
                                    .collect(),
                            ),
                        )
                    };
                    Alternative {
                        pattern: pos::spanned(
                            span,
                            Pattern::Tuple {
                                typ: Type::hole(),
                                elems: vec![
                                    ctor_pattern(l_pattern_args),
                                    ctor_pattern(r_pattern_args),
                                ],
                            },
                        ),
                        expr,
                    }
                })
                .collect();
            Expr::Match(matcher, alts)
        }
        Type::Record(ref row) => {
            let l_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}_l", field.name.declared_name())))
                })
                .collect();
            let r_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}_r", field.name.declared_name())))
                })
                .collect();

            let expr = generate_and_chain(symbols, &mut l_symbols.iter().zip(&r_symbols));
            let generate_record_pattern = |symbols| {
                pos::spanned(
                    span,
                    Pattern::Record {
                        implicit_import: None,
                        typ: Type::hole(),
                        types: Vec::new(),
                        fields: row_iter(row)
                            .zip(symbols)
                            .map(|(field, bind)| PatternField {
                                name: pos::spanned(span, field.name.clone()),
                                value: Some(pos::spanned(span, Pattern::Ident(bind))),
                            })
                            .collect(),
                    },
                )
            };
            Expr::Match(
                matcher,
                vec![Alternative {
                    pattern: pos::spanned(
                        span,
                        Pattern::Tuple {
                            elems: vec![
                                generate_record_pattern(l_symbols),
                                generate_record_pattern(r_symbols),
                            ],
                            typ: Type::hole(),
                        },
                    ),
                    expr,
                }],
            )
        }
        _ => return Err("Unable to derive eq for this type".into()),
    };
    let eq = TypedIdent::new(symbols.symbol("eq"));
    let eq_record_expr = Expr::LetBindings(
        vec![ValueBinding {
            name: pos::spanned(span, Pattern::Ident(eq.clone())),
            args: [l, r]
                .iter()
                .map(|arg| Argument::explicit(pos::spanned(span, TypedIdent::new(arg.clone()))))
                .collect(),
            expr: pos::spanned(span, comparison_expr),
            metadata: Default::default(),
            typ: Some(Type::function(
                vec![
                    Type::ident(bind.alias.value.name.clone()),
                    Type::ident(bind.alias.value.name.clone()),
                ],
                Type::hole(),
            )),
            resolved_type: Type::hole(),
        }],
        Box::new(pos::spanned(
            span,
            Expr::Record {
                typ: Type::hole(),
                types: Vec::new(),
                exprs: vec![ExprField {
                    metadata: Default::default(),
                    name: pos::spanned(span, symbols.symbol("==")),
                    value: Some(ident(span, eq.name.clone())),
                }],
                base: None,
            },
        )),
    );
    Ok(ValueBinding {
        name: pos::spanned(span, Pattern::Ident(TypedIdent::new(Symbol::from("eq")))),
        args: Vec::new(),
        expr: pos::spanned(span, eq_record_expr),
        metadata: Default::default(),
        typ: Some(Type::app(
            Type::ident(symbols.symbol("Eq")),
            collect![Type::ident(bind.alias.value.name.clone())],
        )),
        resolved_type: Type::hole(),
    })
}
