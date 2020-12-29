use crate::base::{
    ast::{
        self, Alternative, Argument, Expr, ExprField, Pattern, TypeBinding, TypedIdent,
        ValueBinding,
    },
    pos,
    symbol::{Symbol, Symbols},
    types::{ctor_args, remove_forall, row_iter, Type, TypeContext},
};

use crate::macros::Error;

use crate::derive::*;

pub fn generate<'ast>(
    mut arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    bind: &TypeBinding<'ast, Symbol>,
) -> Result<ValueBinding<'ast, Symbol>, Error> {
    let span = bind.name.span;

    let eq = TypedIdent::new(symbols.simple_symbol("eq"));
    let l = Symbol::from("l");
    let r = Symbol::from("r");

    let matcher = arena.alloc(pos::spanned(
        span,
        Expr::Tuple {
            typ: Type::hole(),
            elems: arena.alloc_extend(vec![ident(span, l.clone()), ident(span, r.clone())]),
        },
    ));

    let generate_and_chain = |symbols: &mut Symbols,
                              iter: &mut dyn Iterator<
        Item = (&(bool, TypedIdent<Symbol>), &TypedIdent<Symbol>),
    >| {
        iter.fold(None, |acc, (&(self_type, ref l), r)| {
            let equal_symbol = if self_type {
                eq.name.clone()
            } else {
                symbols.simple_symbol("==")
            };

            let eq_check = arena.app(
                span,
                equal_symbol,
                vec![
                    ident(span, l.name.clone()).into(),
                    ident(span, r.name.clone()),
                ],
            );

            Some(match acc {
                Some(acc) => arena.infix(span, acc, symbols.simple_symbol("&&"), eq_check),
                None => eq_check,
            })
        })
        .unwrap_or_else(|| ident(span, symbols.simple_symbol("True")))
    };

    let comparison_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let catch_all_alternative = Alternative {
                pattern: pos::spanned(
                    span,
                    Pattern::Ident(TypedIdent::new(symbols.simple_symbol("_"))),
                ),
                expr: ident(span, symbols.simple_symbol("False")),
            };

            let alts: Vec<_> = row_iter(variants)
                .map(|variant| {
                    let l_pattern_args: Vec<_> = ctor_args(&variant.typ)
                        .map(|field| {
                            (
                                is_self_type(&bind.alias.value.name, field),
                                TypedIdent::new(Symbol::from("arg_l")),
                            )
                        })
                        .collect();
                    let r_pattern_args: Vec<_> = ctor_args(&variant.typ)
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
                                TypedIdent::new(variant.name.value.clone()),
                                arena.alloc_extend(
                                    pattern_args
                                        .into_iter()
                                        .map(|arg| pos::spanned(span, Pattern::Ident(arg))),
                                ),
                            ),
                        )
                    };
                    Alternative {
                        pattern: pos::spanned(
                            span,
                            Pattern::Tuple {
                                typ: Type::hole(),
                                elems: arena.alloc_extend(vec![
                                    ctor_pattern(l_pattern_args.into_iter().map(|t| t.1).collect()),
                                    ctor_pattern(r_pattern_args),
                                ]),
                            },
                        ),
                        expr,
                    }
                })
                .chain(Some(catch_all_alternative))
                .collect();
            Expr::Match(matcher, arena.alloc_extend(alts))
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
                        fields: arena.alloc_extend(row_iter(row).zip(symbols).map(
                            |(field, bind)| PatternField::Value {
                                name: field.name.clone(),
                                value: Some(pos::spanned(span, Pattern::Ident(bind))),
                            },
                        )),
                    },
                )
            };
            Expr::Match(
                matcher,
                arena.alloc_extend(vec![Alternative {
                    pattern: pos::spanned(
                        span,
                        Pattern::Tuple {
                            elems: arena.alloc_extend(vec![
                                generate_record_pattern(
                                    l_symbols.into_iter().map(|t| t.1).collect(),
                                ),
                                generate_record_pattern(r_symbols),
                            ]),
                            typ: Type::hole(),
                        },
                    ),
                    expr,
                }]),
            )
        }
        _ => return Err(Error::message("Unable to derive eq for this type")),
    };

    let mut self_type = {
        let mut arena = arena;
        move || bind.alias.value.self_type(&mut arena)
    };

    let eq_record_expr =
        Expr::rec_let_bindings(
            arena,
            vec![ValueBinding {
                name: pos::spanned(span, Pattern::Ident(eq.clone())),
                args: arena.alloc_extend([l, r].iter().map(|arg| {
                    Argument::explicit(pos::spanned(span, TypedIdent::new(arg.clone())))
                })),
                expr: pos::spanned(span, comparison_expr),
                metadata: Default::default(),
                typ: Some(
                    arena
                        .clone()
                        .function(vec![self_type(), self_type()], arena.hole()),
                ),
                resolved_type: Type::hole(),
            }],
            pos::spanned(
                span,
                Expr::Record {
                    typ: Type::hole(),
                    types: &mut [],
                    exprs: arena.alloc_extend(vec![ExprField {
                        metadata: Default::default(),
                        name: pos::spanned(span, symbols.simple_symbol("==")),
                        value: Some(ident(span, eq.name.clone())),
                    }]),
                    base: None,
                },
            ),
        );

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.simple_symbol(format!(
                "eq_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: &mut [],
        expr: pos::spanned(span, eq_record_expr),
        metadata: Default::default(),
        typ: Some(binding_type(arena, symbols, span, "Eq", self_type(), bind)),
        resolved_type: Type::hole(),
    })
}
