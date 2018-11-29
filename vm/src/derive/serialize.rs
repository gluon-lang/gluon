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

    let serialize_fn = TypedIdent::new(symbols.symbol("serialize"));

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

                    let map = app(
                        span,
                        symbols.symbol("singleton"),
                        vec![literal(span, symbol.name.declared_name()), serialize_field],
                    );

                    Some(match prev {
                        Some(prev) => infix(span, prev, symbols.symbol("<>"), map),
                        None => map,
                    })
                })
                .unwrap_or_else(|| ident(span, symbols.symbol("empty")));

            let construct_object_expr = app(
                span,
                symbols.symbol("Object"),
                vec![paren(span, construct_map_expr)],
            );

            let expr = sequence_actions(
                symbols,
                span,
                &field_symbols,
                construct_object_expr,
                &mut |symbol| {
                    app(
                        span,
                        serialize_fn.name.clone(),
                        vec![ident(span, symbol.clone())],
                    )
                },
            );

            pos::spanned(
                span,
                Expr::Match(
                    Box::new(ident(span, x.clone())),
                    vec![Alternative {
                        pattern: generate_record_pattern(span, row, field_symbols),
                        expr,
                    }],
                ),
            )
        }
        Type::Variant(ref row) => {
            let alts = row_iter(row)
                .map(|variant| {
                    let pattern_args: Vec<_> = row_iter(&variant.typ)
                        .enumerate()
                        .map(|(i, _typ)| TypedIdent::new(Symbol::from(format!("arg_{}", i))))
                        .collect();

                    let expr = {
                        if pattern_args.len() > 1 {
                            return Err(format!(
                                "Variants with more than 1 argument is not yet supported"
                            )
                            .into());
                        }

                        if pattern_args.is_empty() {
                            app(
                                span,
                                serialize_fn.name.clone(),
                                vec![pos::spanned(
                                    span,
                                    Expr::Tuple {
                                        elems: vec![],
                                        typ: Type::hole(),
                                    },
                                )],
                            )
                        } else {
                            let arg = &pattern_args[0];
                            app(
                                span,
                                serialize_fn.name.clone(),
                                vec![ident(span, arg.name.clone())],
                            )
                        }
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
                    Ok(Alternative {
                        pattern: ctor_pattern(pattern_args),
                        expr,
                    })
                })
                .collect::<Result<_, Error>>()?;

            pos::spanned(span, Expr::Match(Box::new(ident(span, x.clone())), alts))
        }

        _ => return Err("Unable to derive Deserialize for this type".into()),
    };

    let serialization_import = generate_import_(
        span,
        symbols,
        &["ValueSerializer", "Value"],
        &["serialize"],
        true,
        "std.json.ser",
    );
    let functor_import = generate_import(span, symbols, &[], &["map"], "std.functor");
    let applicative_import = generate_import(span, symbols, &[], &["<*>"], "std.applicative");
    let map_import = generate_import_(span, symbols, &[], &["singleton", "empty"], true, "std.map");
    let semigroup_import = generate_import(span, symbols, &[], &["<>"], "std.semigroup");
    let result_import = generate_import_(span, symbols, &[], &[], true, "std.result");

    let serialize_ = TypedIdent::new(symbols.symbol("serialize_"));
    let serializer_binding = ValueBinding {
        name: pos::spanned(span, Pattern::Ident(serialize_.clone())),
        args: vec![Argument::explicit(pos::spanned(
            span,
            TypedIdent::new(x.clone()),
        ))],
        expr: serializer_expr,
        metadata: Default::default(),
        typ: Some(Type::function(collect![self_type.clone()], Type::hole())),
        resolved_type: Type::hole(),
    };

    let export_expr = pos::spanned(
        span,
        Expr::Record {
            typ: Type::hole(),
            types: Vec::new(),
            exprs: vec![ExprField {
                metadata: Default::default(),
                name: pos::spanned(span, symbols.symbol("serialize")),
                value: Some(ident(span, serialize_.name.clone())),
            }],
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
        pos::spanned(span, Expr::let_binding(bind, expr))
    });

    Ok(ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Ident(TypedIdent::new(symbols.symbol(format!(
                "serialize_{}",
                bind.alias.value.name.declared_name()
            )))),
        ),
        args: Vec::new(),
        expr: serializer_record_expr,
        metadata: Default::default(),
        typ: Some(binding_type(symbols, "Serialize", self_type, bind)),
        resolved_type: Type::hole(),
    })
}
