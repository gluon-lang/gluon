use crate::base::{
    ast::{AstType, Expr, ExprField, Pattern, TypeBinding, TypedIdent, ValueBinding},
    pos,
    symbol::{Symbol, Symbols},
    types::{remove_forall, row_iter, Type},
};

use crate::macros::Error;

use crate::derive::*;

pub fn generate(
    symbols: &mut Symbols,
    bind: &TypeBinding<Symbol>,
) -> Result<ValueBinding<Symbol>, Error> {
    let span = bind.name.span;

    let deserializer_fn = TypedIdent::new(symbols.simple_symbol("deserializer"));

    let field_deserialize = symbols.simple_symbol("field");
    let deserializer_ident = ident(span, symbols.simple_symbol("deserializer"));

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

            sequence_actions(
                symbols,
                span,
                &field_symbols,
                pos::spanned(
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
                ),
                &mut |field| {
                    app(
                        span,
                        field_deserialize.clone(),
                        vec![
                            literal(span, field.declared_name()),
                            deserializer_ident.clone(),
                        ],
                    )
                },
            )
        }
        Type::Variant(ref row) => row_iter(row)
            .fold(None, |acc, variant| {
                let deserialize_variant = app(
                    span,
                    symbols.simple_symbol("map"),
                    vec![
                        ident(span, variant.name.clone()),
                        deserializer_ident.clone(),
                    ],
                );
                Some(match acc {
                    Some(prev) => infix(
                        span,
                        prev,
                        symbols.simple_symbol("<|>"),
                        deserialize_variant,
                    ),
                    None => deserialize_variant,
                })
            })
            .unwrap(),
        _ => return Err("Unable to derive Deserialize for this type".into()),
    };

    let serialization_import = generate_import_(
        span,
        symbols,
        &["ValueDeserializer"],
        &["deserializer", "field"],
        true,
        "std.json.de",
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
            Type::ident(symbols.simple_symbol("ValueDeserializer")),
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
                name: pos::spanned(span, symbols.simple_symbol("deserializer")),
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
    ]
    .into_iter()
    .rev()
    .fold(export_record_expr, |expr, bind| {
        pos::spanned(span, Expr::let_binding(bind, expr))
    });

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.simple_symbol(format!(
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
