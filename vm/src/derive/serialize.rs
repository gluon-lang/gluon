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

    let x = Symbol::from("x");

    let serialize_fn = symbols.simple_symbol("serialize");

    let mut self_type = {
        let mut arena = arena;
        move || bind.alias.value.self_type(&mut arena)
    };

    let serializer_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Record(ref row) => {
            let field_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}", field.name.declared_name())))
                })
                .collect();

            let construct_map_expr = field_symbols
                .iter()
                .fold(None, |prev, symbol| {
                    let serialize_field = ident(span, symbol.name.clone());

                    let map = arena.app(
                        span,
                        symbols.simple_symbol("singleton"),
                        vec![literal(span, symbol.name.declared_name()), serialize_field],
                    );

                    Some(match prev {
                        Some(prev) => arena.infix(span, prev, symbols.simple_symbol("<>"), map),
                        None => map,
                    })
                })
                .unwrap_or_else(|| ident(span, symbols.simple_symbol("empty")));

            let construct_object_expr = arena.app(
                span,
                symbols.simple_symbol("Object"),
                vec![arena.paren(span, construct_map_expr)],
            );

            let expr = arena.sequence_actions(
                symbols,
                span,
                &field_symbols,
                construct_object_expr,
                &mut |symbol| {
                    arena.app(
                        span,
                        serialize_fn.clone(),
                        Some(ident(span, symbol.clone())),
                    )
                },
            );

            pos::spanned(
                span,
                Expr::Match(
                    arena.alloc(ident(span, x.clone())),
                    arena.alloc_extend(Some(Alternative {
                        pattern: arena.generate_record_pattern(span, row, field_symbols),
                        expr,
                    })),
                ),
            )
        }
        Type::Variant(ref row) => {
            let alts: Vec<_> = row_iter(row)
                .map(|variant| {
                    let pattern_args: Vec<_> = ctor_args(&variant.typ)
                        .enumerate()
                        .map(|(i, _typ)| TypedIdent::new(Symbol::from(format!("arg_{}", i))))
                        .collect();

                    let expr = {
                        if pattern_args.len() > 1 {
                            return Err(Error::message(format!(
                                "Variants with more than 1 argument is not yet supported"
                            )));
                        }

                        if pattern_args.is_empty() {
                            arena.app(
                                span,
                                serialize_fn.clone(),
                                vec![pos::spanned(
                                    span,
                                    Expr::Tuple {
                                        elems: &mut [],
                                        typ: Type::hole(),
                                    },
                                )],
                            )
                        } else {
                            let arg = &pattern_args[0];
                            arena.app(
                                span,
                                serialize_fn.clone(),
                                vec![ident(span, arg.name.clone())],
                            )
                        }
                    };

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
                    Ok(Alternative {
                        pattern: ctor_pattern(pattern_args),
                        expr,
                    })
                })
                .collect::<Result<_, Error>>()?;

            pos::spanned(
                span,
                Expr::Match(
                    arena.alloc(ident(span, x.clone())),
                    arena.alloc_extend(alts),
                ),
            )
        }

        _ => return Err(Error::message("Unable to derive Deserialize for this type")),
    };

    let serialization_import = arena.generate_import_(
        span,
        symbols,
        &["ValueSerializer", "Value"],
        &["serialize"],
        true,
        "std.json.ser",
    );
    let functor_import = arena.generate_import(span, symbols, &[], &["map"], "std.functor");
    let applicative_import = arena.generate_import(span, symbols, &[], &["<*>"], "std.applicative");
    let map_import =
        arena.generate_import_(span, symbols, &[], &["singleton", "empty"], true, "std.map");
    let semigroup_import = arena.generate_import(span, symbols, &[], &["<>"], "std.semigroup");
    let result_import = arena.generate_import_(span, symbols, &[], &[], true, "std.result");

    let serialize_ = TypedIdent::new(symbols.simple_symbol("serialize_"));
    let serializer_binding = ValueBinding {
        name: pos::spanned(span, Pattern::Ident(serialize_.clone())),
        args: arena.alloc_extend(Some(Argument::explicit(pos::spanned(
            span,
            TypedIdent::new(x.clone()),
        )))),
        expr: serializer_expr,
        metadata: Default::default(),
        typ: Some(arena.clone().function(Some(self_type()), arena.hole())),
        resolved_type: Type::hole(),
    };

    let export_expr = pos::spanned(
        span,
        Expr::Record {
            typ: Type::hole(),
            types: &mut [],
            exprs: arena.alloc_extend(Some(ExprField {
                metadata: Default::default(),
                name: pos::spanned(span, symbols.simple_symbol("serialize")),
                value: Some(ident(span, serialize_.name.clone())),
            })),
            base: None,
        },
    );

    let serializer_record_expr = vec![
        result_import,
        serialization_import,
        functor_import,
        applicative_import,
        map_import,
        semigroup_import,
        serializer_binding,
    ]
    .into_iter()
    .rev()
    .fold(export_expr, |expr, bind| {
        pos::spanned(span, Expr::let_binding(arena, bind, expr))
    });

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.simple_symbol(format!(
                "serialize_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: &mut [],
        expr: serializer_record_expr,
        metadata: Default::default(),
        typ: Some(binding_type(
            arena,
            symbols,
            span,
            "Serialize",
            self_type(),
            bind,
        )),
        resolved_type: Type::hole(),
    })
}
