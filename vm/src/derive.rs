use base::ast::{
    Alternative, Argument, Expr, ExprField, Literal, Pattern, PatternField, SpannedExpr,
    TypeBinding, TypedIdent, ValueBinding,
};
use base::metadata::Attribute;
use base::pos::{self, BytePos, Span};
use base::symbol::{Symbol, Symbols};
use base::types::{arg_iter, row_iter, Type};

use macros::Error;

pub fn generate(
    symbols: &mut Symbols,
    derive: &Attribute,
    bind: &TypeBinding<Symbol>,
) -> Result<Vec<ValueBinding<Symbol>>, Error> {
    match derive.arguments {
        Some(ref args) => args
            .split(',')
            .map(|s| s.trim())
            .map(|arg| match arg {
                "Eq" => generate_eq(symbols, bind),
                "Show" => generate_show(symbols, bind),
                _ => panic!(),
            })
            .collect(),
        _ => Err("Invalid `derive` attribute".into()),
    }
}

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
            let catch_all_alternative = Alternative {
                pattern: pos::spanned(span, Pattern::Ident(TypedIdent::new(symbols.symbol("_")))),
                expr: ident(span, symbols.symbol("False")),
            };

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
                .chain(Some(catch_all_alternative))
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
