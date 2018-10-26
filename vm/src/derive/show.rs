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

    let x = Symbol::from("x");
    let show_fn = TypedIdent::new(symbols.symbol("show_"));

    let show_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let alts = row_iter(variants)
                .map(|variant| {
                    let pattern_args: Vec<_> = row_iter(&variant.typ)
                        .enumerate()
                        .map(|(i, field)| {
                            (
                                is_self_type(&bind.alias.value.name, &field.typ),
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

    let show_record_expr = Expr::rec_let_bindings(
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
        pos::spanned(
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
        ),
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
