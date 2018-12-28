use crate::base::ast::{
    Argument, AstType, Expr, Lambda, Literal, Pattern, PatternField, SpannedExpr, SpannedPattern,
    TypeBinding, TypedIdent, ValueBinding,
};
use crate::base::metadata::Attribute;
use crate::base::pos::{self, BytePos, Span};
use crate::base::symbol::{Symbol, Symbols};
use crate::base::types::{row_iter, Type};

use crate::macros::Error;

mod deserialize;
mod eq;
mod serialize;
mod show;

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
                    "Eq" => eq::generate(symbols, bind),
                    "Show" => show::generate(symbols, bind),
                    "Deserialize" => deserialize::generate(symbols, bind),
                    "Serialize" => serialize::generate(symbols, bind),
                    _ => return Err(format!("`{}` is not a type that can be derived", arg)),
                })
            })
            .collect::<Result<_, _>>()?,
        _ => Err("Invalid `derive` attribute".into()),
    }
}

fn sequence_actions(
    symbols: &mut Symbols,
    span: Span<BytePos>,
    field_symbols: &[TypedIdent<Symbol>],
    packed_expr: SpannedExpr<Symbol>,
    action: &mut FnMut(&Symbol) -> SpannedExpr<Symbol>,
) -> SpannedExpr<Symbol> {
    let pack_record = pos::spanned(
        span,
        Expr::Lambda(Lambda {
            args: field_symbols
                .iter()
                .cloned()
                .map(|id| Argument::explicit(pos::spanned(span, id)))
                .collect(),
            body: Box::new(packed_expr),
            id: TypedIdent::new(symbols.symbol("pack_record")),
        }),
    );
    let map_expr = app(
        span,
        symbols.symbol("map"),
        vec![
            paren(span, pack_record),
            paren(span, action(&field_symbols.first().expect("FIXME").name)),
        ],
    );

    field_symbols.iter().skip(1).fold(map_expr, |prev, symbol| {
        let deserialize_field = action(&symbol.name);
        infix(span, prev, symbols.symbol("<*>"), deserialize_field)
    })
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
    generate_import_(span, symbols, type_fields, fields, false, import)
}

fn generate_import_(
    span: Span<BytePos>,
    symbols: &mut Symbols,
    type_fields: &[&str],
    fields: &[&str],
    implicit_import: bool,
    import: &str,
) -> ValueBinding<Symbol> {
    ValueBinding {
        name: pos::spanned(
            span,
            Pattern::Record {
                implicit_import: if implicit_import {
                    Some(pos::spanned(span, Symbol::from("implicit_import")))
                } else {
                    None
                },
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
