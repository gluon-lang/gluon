use crate::base::ast::{
    self, Alternative, Argument, AstType, Expr, ExprField, Pattern, TypeBinding, TypedIdent,
    ValueBinding,
};
use crate::base::pos;
use crate::base::symbol::{Symbol, Symbols};
use crate::base::types::{ctor_args, remove_forall, row_iter, Type};

use crate::macros::Error;

use crate::derive::*;

pub fn generate<'ast>(
    arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<'ast, Symbol>, Error> {
    let span = bind.name.span;

    let x = Symbol::from("x");
    let show_fn = TypedIdent::new(symbols.simple_symbol("show_"));

    let show_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Variant(ref variants) => {
            let alts: Vec<_> = row_iter(variants)
                .map(|variant| {
                    let pattern_args: Vec<_> = ctor_args(&variant.typ)
                        .enumerate()
                        .map(|(i, field)| {
                            (
                                is_self_type(&bind.alias.value.name, field),
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
                                    symbols.simple_symbol("show")
                                };
                                let show = arena.infix(
                                    span,
                                    literal(span, "("),
                                    symbols.simple_symbol("++"),
                                    arena.infix(
                                        span,
                                        arena.app(
                                            span,
                                            show_function,
                                            vec![ident(span, x.name.clone())],
                                        ),
                                        symbols.simple_symbol("++"),
                                        literal(span, ")"),
                                    ),
                                );
                                arena.infix(
                                    span,
                                    acc,
                                    symbols.simple_symbol("++"),
                                    arena.infix(
                                        span,
                                        literal(span, " "),
                                        symbols.simple_symbol("++"),
                                        show,
                                    ),
                                )
                            })
                    };

                    let ctor_pattern = |pattern_args: Vec<_>| {
                        pos::spanned(
                            span,
                            Pattern::Constructor(
                                TypedIdent::new(variant.name.clone()),
                                arena.alloc_extend(
                                    pattern_args
                                        .into_iter()
                                        .map(|arg| pos::spanned(span, Pattern::Ident(arg))),
                                ),
                            ),
                        )
                    };
                    Alternative {
                        pattern: ctor_pattern(pattern_args.into_iter().map(|t| t.1).collect()),
                        expr,
                    }
                })
                .collect();
            Expr::Match(
                arena.alloc(ident(span, x.clone())),
                arena.alloc_extend(alts),
            )
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
                        let show = arena.app(
                            span,
                            symbols.simple_symbol("show"),
                            vec![ident(span, x.name.clone())],
                        );

                        let show_field = arena.infix(
                            span,
                            acc,
                            symbols.simple_symbol("++"),
                            arena.infix(
                                span,
                                literal(span, &format!("{} = ", x.name.declared_name())),
                                symbols.simple_symbol("++"),
                                show,
                            ),
                        );

                        let last = i == field_symbols.len() - 1;
                        let suffix = if last { " " } else { ", " };
                        arena.infix(
                            span,
                            show_field,
                            symbols.simple_symbol("++"),
                            literal(span, suffix),
                        )
                    });

                arena.infix(
                    span,
                    show_expr,
                    symbols.simple_symbol("++"),
                    literal(span, "}"),
                )
            };
            Expr::Match(
                arena.alloc(ident(span, x.clone())),
                arena.alloc_extend(Some(Alternative {
                    pattern: arena.generate_record_pattern(span, row, field_symbols),
                    expr,
                })),
            )
        }
        _ => return Err(Error::message("Unable to derive Show for this type")),
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
        arena,
        Some(ValueBinding {
            name: pos::spanned(span, Pattern::Ident(show_fn.clone())),
            args: arena.alloc_extend(Some(Argument::explicit(pos::spanned(
                span,
                TypedIdent::new(x.clone()),
            )))),
            expr: pos::spanned(span, show_expr),
            metadata: Default::default(),
            typ: Some(Type::function(vec![self_type.clone()], Type::string())),
            resolved_type: Type::hole(),
        }),
        pos::spanned(
            span,
            Expr::Record {
                typ: Type::hole(),
                types: &mut [],
                exprs: arena.alloc_extend(Some(ExprField {
                    metadata: Default::default(),
                    name: pos::spanned(span, symbols.simple_symbol("show")),
                    value: Some(ident(span, show_fn.name.clone())),
                })),
                base: None,
            },
        ),
    );

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.simple_symbol(format!(
                "show_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: &mut [],
        expr: pos::spanned(span, show_record_expr),
        metadata: Default::default(),
        typ: Some(binding_type(symbols, "Show", self_type, bind)),
        resolved_type: Type::hole(),
    })
}
