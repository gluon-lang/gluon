use crate::base::{
    ast::{self, Expr, ExprField, Pattern, TypeBinding, TypedIdent, ValueBinding},
    pos,
    symbol::{Symbol, Symbols},
    types::{remove_forall, row_iter, KindedIdent, Type, TypeContext},
};

use crate::macros::Error;

use crate::derive::*;

pub fn generate<'ast>(
    mut arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    bind: &TypeBinding<'ast, Symbol>,
) -> Result<ValueBinding<'ast, Symbol>, Error> {
    let span = bind.name.span;

    let deserializer_fn = TypedIdent::new(symbols.simple_symbol("deserializer"));

    let field_deserialize = symbols.simple_symbol("field");
    let deserializer_ident = {
        let id = symbols.simple_symbol("deserializer");
        move || ident(span, id.clone())
    };

    let mut self_type = {
        let mut arena = arena;
        move || bind.alias.value.self_type(&mut arena)
    };

    let deserializer_expr = match **remove_forall(bind.alias.value.unresolved_type()) {
        Type::Record(ref row) => {
            let field_symbols: Vec<_> = row_iter(row)
                .map(|field| {
                    TypedIdent::new(Symbol::from(format!("{}", field.name.declared_name())))
                })
                .collect();

            arena.sequence_actions(
                symbols,
                span,
                &field_symbols,
                pos::spanned(
                    span,
                    Expr::Record {
                        exprs: arena.alloc_extend(field_symbols.iter().map(|id| ExprField {
                            name: pos::spanned(span, id.name.clone()),
                            value: None,
                            metadata: Default::default(),
                        })),
                        types: &mut [],
                        typ: Type::hole(),
                        base: None,
                    },
                ),
                &mut |field| {
                    arena.app(
                        span,
                        field_deserialize.clone(),
                        vec![literal(span, field.declared_name()), deserializer_ident()],
                    )
                },
            )
        }
        Type::Variant(ref row) => row_iter(row)
            .fold(None, |acc, variant| {
                let deserialize_variant = arena.app(
                    span,
                    symbols.simple_symbol("map"),
                    vec![
                        ident(variant.name.span, variant.name.value.clone()),
                        deserializer_ident(),
                    ],
                );
                Some(match acc {
                    Some(prev) => arena.infix(
                        span,
                        prev,
                        symbols.simple_symbol("<|>"),
                        deserialize_variant,
                    ),
                    None => deserialize_variant,
                })
            })
            .unwrap(),
        _ => return Err(Error::message("Unable to derive Deserialize for this type")),
    };

    let serialization_import = arena.generate_import_(
        span,
        symbols,
        &["ValueDeserializer"],
        &["deserializer", "field"],
        true,
        "std.json.de",
    );
    let functor_import = arena.generate_import(span, symbols, &[], &["map"], "std.functor");
    let applicative_import = arena.generate_import(span, symbols, &[], &["<*>"], "std.applicative");
    let alternative_import = arena.generate_import(span, symbols, &[], &["<|>"], "std.alternative");

    let deserializer_binding = ValueBinding {
        name: pos::spanned(span, Pattern::Ident(deserializer_fn.clone())),
        args: &mut [],
        expr: deserializer_expr,
        metadata: Default::default(),
        typ: Some(TypeContext::app(
            &mut arena.clone(),
            arena.ident(KindedIdent::new(symbols.simple_symbol("ValueDeserializer"))),
            arena.clone().alloc_extend(Some(self_type())),
        )),
        resolved_type: Type::hole(),
    };

    let export_record_expr = pos::spanned(
        span,
        Expr::Record {
            typ: Type::hole(),
            types: &mut [],
            exprs: arena.alloc_extend(vec![ExprField {
                metadata: Default::default(),
                name: pos::spanned(span, symbols.simple_symbol("deserializer")),
                value: Some(ident(span, deserializer_fn.name.clone())),
            }]),
            base: None,
        },
    );

    let deserializer_record_expr = vec![
        serialization_import,
        functor_import,
        applicative_import,
        alternative_import,
        deserializer_binding,
    ]
    .into_iter()
    .rev()
    .fold(export_record_expr, |expr, bind| {
        pos::spanned(span, Expr::let_binding(arena, bind, expr))
    });

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.simple_symbol(format!(
                "deserialize_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: &mut [],
        expr: deserializer_record_expr,
        metadata: Default::default(),
        typ: Some(binding_type(
            arena,
            symbols,
            span,
            "Deserialize",
            self_type(),
            bind,
        )),
        resolved_type: Type::hole(),
    })
}
