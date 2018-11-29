use base::ast::{
    Alternative, Argument, AstType, Expr, ExprField, Pattern, TypeBinding, TypedIdent, ValueBinding,
};
use base::pos;
use base::symbol::{Symbol, Symbols};
use base::types::{remove_forall, row_iter, Type};

use macros::Error;

use derive::*;

pub fn generate(
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
            })
            .unwrap_or_else(|| ident(span, symbols.symbol("True")))
        };

    let comparison_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let catch_all_alternative = Alternative {
                pattern: pos::spanned(span, Pattern::Ident(TypedIdent::new(symbols.symbol("_")))),
                expr: ident(span, symbols.symbol("False")),
            };

            let alts = row_iter(variants)
                .map(|variant| {
                    let l_pattern_args: Vec<_> = row_iter(&variant.typ)
                        .map(|field| {
                            (
                                is_self_type(&bind.alias.value.name, &field.typ),
                                TypedIdent::new(Symbol::from("arg_l")),
                            )
                        })
                        .collect();
                    let r_pattern_args: Vec<_> = row_iter(&variant.typ)
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

    let eq_record_expr = Expr::rec_let_bindings(
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
        pos::spanned(
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
        ),
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
