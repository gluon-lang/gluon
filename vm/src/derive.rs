use base::ast::{
    Alternative, Argument, AstType, Expr, ExprField, Lambda, Literal, Pattern, PatternField,
    SpannedExpr, SpannedPattern, TypeBinding, TypedIdent, ValueBinding,
};
use base::metadata::Attribute;
use base::pos::{self, BytePos, Span};
use base::symbol::{Symbol, Symbols};
use base::types::{arg_iter, remove_forall, row_iter, Type};

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
            .map(|arg| {
                Ok(match arg {
                    "Eq" => generate_eq(symbols, bind),
                    "Show" => generate_show(symbols, bind),
                    "Deserialize" => generate_deserialize(symbols, bind),
                    _ => return Err(format!("`{}` is not a type that can be derived", arg)),
                })
            })
            .collect::<Result<_, _>>()?,
        _ => Err("Invalid `derive` attribute".into()),
    }
}

fn generate_record_pattern<I>(
    span: Span<BytePos>,
    row: &AstType<Symbol>,
    symbols: I,
) -> SpannedPattern<Symbol>
where
    I: IntoIterator<Item = TypedIdent<Symbol>>,
{
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
}

fn generate_import(
    span: Span<BytePos>,
    symbols: &mut Symbols,
    type_fields: &[&str],
    fields: &[&str],
    import: &str,
) -> ValueBinding<Symbol> {
    ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Record {
                implicit_import: None,
                typ: Type::hole(),
                types: type_fields
                    .iter()
                    .map(|f| PatternField {
                        name: pos::spanned(span, symbols.symbol(*f)),
                        value: None,
                    })
                    .collect(),
                fields: fields
                    .iter()
                    .map(|f| PatternField {
                        name: pos::spanned(span, symbols.symbol(*f)),
                        value: None,
                    })
                    .collect(),
            },
        ),
        args: Vec::new(),
        expr: app(
            span,
            symbols.symbol("import!"),
            vec![project(span, symbols, import)],
        ),
        metadata: Default::default(),
        typ: None,
        resolved_type: Type::hole(),
    }
}

fn project(span: Span<BytePos>, symbols: &mut Symbols, p: &str) -> SpannedExpr<Symbol> {
    p.split('.')
        .fold(None, |acc, name| {
            let symbol = symbols.symbol(name);
            Some(match acc {
                Some(expr) => {
                    pos::spanned(span, Expr::Projection(Box::new(expr), symbol, Type::hole()))
                }
                None => ident(span, symbol),
            })
        })
        .unwrap()
}

fn ident(span: Span<BytePos>, s: Symbol) -> SpannedExpr<Symbol> {
    pos::spanned(span, Expr::Ident(TypedIdent::new(s)))
}

fn literal(span: Span<BytePos>, s: &str) -> SpannedExpr<Symbol> {
    pos::spanned(span, Expr::Literal(Literal::String(s.to_string())))
}
fn paren(span: Span<BytePos>, expr: SpannedExpr<Symbol>) -> SpannedExpr<Symbol> {
    pos::spanned(
        span,
        Expr::Tuple {
            elems: vec![expr],
            typ: Type::hole(),
        },
    )
}

fn app(span: Span<BytePos>, func: Symbol, args: Vec<SpannedExpr<Symbol>>) -> SpannedExpr<Symbol> {
    pos::spanned(
        span,
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
        span,
        Expr::Infix {
            lhs: lhs.into(),
            op: pos::spanned(span, TypedIdent::new(op)),
            rhs: rhs.into(),
            implicit_args: Vec::new(),
        },
    )
}

fn is_self_type(self_: &Symbol, typ: &AstType<Symbol>) -> bool {
    match **typ {
        Type::App(ref f, _) => is_self_type(self_, f),
        Type::Alias(ref alias) => alias.name == *self_,
        Type::Ident(ref id) => id == self_,
        _ => false,
    }
}

fn binding_type(
    symbols: &mut Symbols,
    derive_type_name: &str,
    self_type: AstType<Symbol>,
    bind: &TypeBinding<Symbol>,
) -> AstType<Symbol> {
    let derive_type: AstType<_> = Type::ident(symbols.symbol(derive_type_name));
    Type::function_implicit(
        bind.alias
            .value
            .params()
            .iter()
            .cloned()
            .map(|g| Type::app(derive_type.clone(), collect![Type::generic(g)])),
        Type::app(derive_type.clone(), collect![self_type]),
    )
}

fn generate_show(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let x = Symbol::from("x");
    let show_fn = TypedIdent::new(symbols.symbol("show_"));

    let show_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let alts = row_iter(variants)
                .map(|variant| {
                    let pattern_args: Vec<_> = arg_iter(&variant.typ)
                        .enumerate()
                        .map(|(i, typ)| {
                            (
                                is_self_type(&bind.alias.value.name, typ),
                                TypedIdent::new(Symbol::from(format!("arg_{}", i))),
                            )
                        })
                        .collect();

                    let expr = {
                        let open_brace = literal(span, variant.name.declared_name());

                        pattern_args
                            .iter()
                            .fold(open_brace, |acc, &(self_type, ref x)| {
                                let show_function = if self_type {
                                    show_fn.name.clone()
                                } else {
                                    symbols.symbol("show")
                                };
                                let show = infix(
                                    span,
                                    literal(span, "("),
                                    symbols.symbol("++"),
                                    infix(
                                        span,
                                        app(span, show_function, vec![ident(span, x.name.clone())]),
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
                        pattern: ctor_pattern(pattern_args.into_iter().map(|t| t.1).collect()),
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
            Expr::Match(
                Box::new(ident(span, x.clone())),
                vec![Alternative {
                    pattern: generate_record_pattern(span, row, field_symbols),
                    expr,
                }],
            )
        }
        _ => return Err("Unable to derive Show for this type".into()),
    };

    let self_type: AstType<_> = Type::app(
        Type::ident(bind.alias.value.name.clone()),
        bind.alias
            .value
            .params()
            .iter()
            .cloned()
            .map(Type::generic)
            .collect(),
    );

    let show_record_expr = Expr::LetBindings(
        vec![ValueBinding {
            name: pos::spanned(span, Pattern::Ident(show_fn.clone())),
            args: vec![Argument::explicit(pos::spanned(
                span,
                TypedIdent::new(x.clone()),
            ))],
            expr: pos::spanned(span, show_expr),
            metadata: Default::default(),
            typ: Some(Type::function(vec![self_type.clone()], Type::string())),
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
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(
                symbols.symbol(format!("show_{}", bind.alias.value.name.declared_name())),
            )),
        ),
        args: Vec::new(),
        expr: pos::spanned(span, show_record_expr),
        metadata: Default::default(),
        typ: Some(binding_type(symbols, "Show", self_type, bind)),
        resolved_type: Type::hole(),
    })
}

fn generate_eq(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let eq = TypedIdent::new(symbols.symbol("eq"));
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
         iter: &mut Iterator<Item = (&(bool, TypedIdent<Symbol>), &TypedIdent<Symbol>)>| {
            iter.fold(None, |acc, (&(self_type, ref l), r)| {
                let equal_symbol = if self_type {
                    eq.name.clone()
                } else {
                    symbols.symbol("==")
                };

                let eq_check = app(
                    span,
                    equal_symbol,
                    vec![
                        ident(span, l.name.clone()).into(),
                        ident(span, r.name.clone()),
                    ],
                );

                Some(match acc {
                    Some(acc) => infix(span, acc, symbols.symbol("&&"), eq_check),
                    None => eq_check,
                })
            }).unwrap_or_else(|| ident(span, symbols.symbol("True")))
        };

    let comparison_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let catch_all_alternative = Alternative {
                pattern: pos::spanned(span, Pattern::Ident(TypedIdent::new(symbols.symbol("_")))),
                expr: ident(span, symbols.symbol("False")),
            };

            let alts = row_iter(variants)
                .map(|variant| {
                    let l_pattern_args: Vec<_> = arg_iter(&variant.typ)
                        .map(|typ| {
                            (
                                is_self_type(&bind.alias.value.name, typ),
                                TypedIdent::new(Symbol::from("arg_l")),
                            )
                        })
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
                                    ctor_pattern(l_pattern_args.into_iter().map(|t| t.1).collect()),
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
                    (
                        is_self_type(&bind.alias.value.name, &field.typ),
                        TypedIdent::new(Symbol::from(format!("{}_l", field.name.declared_name()))),
                    )
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
                                generate_record_pattern(
                                    l_symbols.into_iter().map(|t| t.1).collect(),
                                ),
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

    let self_type: AstType<_> = Type::app(
        Type::ident(bind.alias.value.name.clone()),
        bind.alias
            .value
            .params()
            .iter()
            .cloned()
            .map(Type::generic)
            .collect(),
    );

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
                vec![self_type.clone(), self_type.clone()],
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
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(
                symbols.symbol(format!("eq_{}", bind.alias.value.name.declared_name())),
            )),
        ),
        args: Vec::new(),
        expr: pos::spanned(span, eq_record_expr),
        metadata: Default::default(),
        typ: Some(binding_type(symbols, "Eq", self_type, bind)),
        resolved_type: Type::hole(),
    })
}

fn generate_deserialize(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let deserializer_fn = TypedIdent::new(symbols.symbol("deserializer"));

    let field_deserialize = symbols.symbol("field");
    let deserializer_ident = ident(span, symbols.symbol("deserializer"));

    let self_type: AstType<_> = Type::app(
        Type::ident(bind.alias.value.name.clone()),
        bind.alias
            .value
            .params()
            .iter()
            .cloned()
            .map(Type::generic)
            .collect(),
    );

    let deserializer_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Record(ref row) => {
            let field_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}", field.name.declared_name())))
                })
                .collect();

            let pack_record = pos::spanned(
                span,
                Expr::Lambda(Lambda {
                    args: field_symbols
                        .iter()
                        .cloned()
                        .map(|id| Argument::explicit(pos::spanned(span, id)))
                        .collect(),
                    body: Box::new(pos::spanned(
                        span,
                        Expr::Record {
                            exprs: field_symbols
                                .iter()
                                .map(|id| ExprField {
                                    name: pos::spanned(span, id.name.clone()),
                                    value: None,
                                    metadata: Default::default(),
                                })
                                .collect(),
                            types: Vec::new(),
                            typ: Type::hole(),
                            base: None,
                        },
                    )),
                    id: TypedIdent::new(symbols.symbol("pack_record")),
                }),
            );
            let map_expr = app(
                span,
                symbols.symbol("map"),
                vec![
                    paren(span, pack_record),
                    paren(
                        span,
                        app(
                            span,
                            field_deserialize.clone(),
                            vec![
                                literal(
                                    span,
                                    field_symbols.first().expect("FIXME").name.declared_name(),
                                ),
                                deserializer_ident.clone(),
                            ],
                        ),
                    ),
                ],
            );

            field_symbols.iter().skip(1).fold(map_expr, |prev, symbol| {
                let deserialize_field = app(
                    span,
                    field_deserialize.clone(),
                    vec![
                        literal(span, symbol.name.declared_name()),
                        deserializer_ident.clone(),
                    ],
                );
                infix(span, prev, symbols.symbol("<*>"), deserialize_field)
            })
        }
        Type::Variant(ref row) => row_iter(row)
            .fold(None, |acc, variant| {
                let deserialize_variant = app(
                    span,
                    symbols.symbol("map"),
                    vec![
                        ident(span, variant.name.clone()),
                        deserializer_ident.clone(),
                    ],
                );
                Some(match acc {
                    Some(prev) => infix(span, prev, symbols.symbol("<|>"), deserialize_variant),
                    None => deserialize_variant,
                })
            })
            .unwrap(),
        _ => return Err("Unable to derive Deserialize for this type".into()),
    };

    let serialization_import = generate_import(
        span,
        symbols,
        &["ValueDeserializer"],
        &[],
        "std.serialization.de",
    );
    let functor_import = generate_import(span, symbols, &[], &["map"], "std.functor");
    let applicative_import = generate_import(span, symbols, &[], &["<*>"], "std.applicative");
    let alternative_import = generate_import(span, symbols, &[], &["<|>"], "std.alternative");

    let deserializer_binding = ValueBinding {
        name: pos::spanned(span, Pattern::Ident(deserializer_fn.clone())),
        args: Vec::new(),
        expr: deserializer_expr,
        metadata: Default::default(),
        typ: Some(Type::app(
            Type::ident(symbols.symbol("ValueDeserializer")),
            collect![self_type.clone()],
        )),
        resolved_type: Type::hole(),
    };

    let export_record_expr = pos::spanned(
        span,
        Expr::Record {
            typ: Type::hole(),
            types: Vec::new(),
            exprs: vec![ExprField {
                metadata: Default::default(),
                name: pos::spanned(span, symbols.symbol("deserializer")),
                value: Some(ident(span, deserializer_fn.name.clone())),
            }],
            base: None,
        },
    );

    let deserializer_record_expr = vec![
        serialization_import,
        functor_import,
        applicative_import,
        alternative_import,
        deserializer_binding,
    ].into_iter()
        .rev()
        .fold(export_record_expr, |expr, bind| {
            pos::spanned(span, Expr::LetBindings(vec![bind], Box::new(expr)))
        });

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.symbol(format!(
                "deserialize_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: Vec::new(),
        expr: deserializer_record_expr,
        metadata: Default::default(),
        typ: Some(binding_type(symbols, "Deserialize", self_type, bind)),
        resolved_type: Type::hole(),
    })
}
