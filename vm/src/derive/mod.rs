use crate::base::{
    ast::{
        self, Argument, AstAlloc, AstType, Expr, Lambda, Literal, Pattern, PatternField,
        SpannedExpr, SpannedPattern, TypeBinding, TypedIdent, ValueBinding,
    },
    metadata::Attribute,
    pos::{self, BytePos, Span},
    symbol::{Symbol, Symbols},
    types::{row_iter, KindedIdent, Type, TypeContext},
};

use crate::macros::Error;

mod deserialize;
mod eq;
mod serialize;
mod show;

pub fn generate<'ast>(
    arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    derive: &Attribute,
    bind: &TypeBinding<'ast, Symbol>,
) -> Result<Vec<ValueBinding<'ast, Symbol>>, Error> {
    match derive.arguments {
        Some(ref args) => args
            .split(',')
            .map(|s| s.trim())
            .map(|arg| {
                Ok(match arg {
                    "Eq" => eq::generate(arena, symbols, bind),
                    "Show" => show::generate(arena, symbols, bind),
                    "Deserialize" => deserialize::generate(arena, symbols, bind),
                    "Serialize" => serialize::generate(arena, symbols, bind),
                    _ => {
                        return Err(Error::message(format!(
                            "`{}` is not a type that can be derived",
                            arg
                        )));
                    }
                })
            })
            .collect::<Result<_, _>>()?,
        _ => Err(Error::message("Invalid `derive` attribute")),
    }
}

impl<'ast> ArenaExt<'ast> for ast::ArenaRef<'_, 'ast, Symbol> {
    fn alloc<T>(self, value: T) -> &'ast mut T
    where
        T: AstAlloc<'ast, Symbol>,
    {
        Self::alloc(self, value)
    }

    fn alloc_extend<T>(self, iter: impl IntoIterator<Item = T>) -> &'ast mut [T]
    where
        T: AstAlloc<'ast, Symbol>,
    {
        Self::alloc_extend(self, iter)
    }
}
pub trait ArenaExt<'ast>: Sized + Copy {
    fn alloc<T>(self, value: T) -> &'ast mut T
    where
        T: AstAlloc<'ast, Symbol>;

    fn alloc_extend<T>(self, iter: impl IntoIterator<Item = T>) -> &'ast mut [T]
    where
        T: AstAlloc<'ast, Symbol>;

    fn sequence_actions(
        self,
        symbols: &mut Symbols,
        span: Span<BytePos>,
        field_symbols: &[TypedIdent<Symbol>],
        packed_expr: SpannedExpr<'ast, Symbol>,
        action: &mut dyn FnMut(&Symbol) -> SpannedExpr<'ast, Symbol>,
    ) -> SpannedExpr<'ast, Symbol> {
        let pack_record = pos::spanned(
            span,
            Expr::Lambda(Lambda {
                args: self.alloc_extend(
                    field_symbols
                        .iter()
                        .cloned()
                        .map(|id| Argument::explicit(pos::spanned(span, id))),
                ),
                body: self.alloc(packed_expr),
                id: TypedIdent::new(symbols.simple_symbol("pack_record")),
            }),
        );
        let map_expr = self.app(
            span,
            symbols.simple_symbol("map"),
            vec![
                self.paren(span, pack_record),
                self.paren(span, action(&field_symbols.first().expect("FIXME").name)),
            ],
        );

        field_symbols.iter().skip(1).fold(map_expr, |prev, symbol| {
            let deserialize_field = action(&symbol.name);
            self.infix(span, prev, symbols.simple_symbol("<*>"), deserialize_field)
        })
    }

    fn generate_record_pattern<I>(
        self,
        span: Span<BytePos>,
        row: &AstType<Symbol>,
        symbols: I,
    ) -> SpannedPattern<'ast, Symbol>
    where
        I: IntoIterator<Item = TypedIdent<Symbol>>,
    {
        pos::spanned(
            span,
            Pattern::Record {
                implicit_import: None,
                typ: Type::hole(),
                fields: self.alloc_extend(row_iter(row).zip(symbols).map(|(field, bind)| {
                    PatternField::Value {
                        name: field.name.clone(),
                        value: Some(pos::spanned(span, Pattern::Ident(bind))),
                    }
                })),
            },
        )
    }

    fn generate_import(
        self,
        span: Span<BytePos>,
        symbols: &mut Symbols,
        type_fields: &[&str],
        fields: &[&str],
        import: &str,
    ) -> ValueBinding<'ast, Symbol> {
        self.generate_import_(span, symbols, type_fields, fields, false, import)
    }

    fn generate_import_(
        self,
        span: Span<BytePos>,
        symbols: &mut Symbols,
        type_fields: &[&str],
        fields: &[&str],
        implicit_import: bool,
        import: &str,
    ) -> ValueBinding<'ast, Symbol> {
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
                    fields: self.alloc_extend(
                        type_fields
                            .iter()
                            .map(|f| (false, f))
                            .chain(fields.iter().map(|f| (true, f)))
                            .map(|(is_value, f)| {
                                if is_value {
                                    PatternField::Value {
                                        name: pos::spanned(span, symbols.simple_symbol(*f)),
                                        value: None,
                                    }
                                } else {
                                    PatternField::Type {
                                        name: pos::spanned(span, symbols.simple_symbol(*f)),
                                    }
                                }
                            }),
                    ),
                },
            ),
            args: &mut [],
            expr: self.app(
                span,
                symbols.simple_symbol("import!"),
                vec![self.project(span, symbols, import)],
            ),
            metadata: Default::default(),
            typ: None,
            resolved_type: Type::hole(),
        }
    }

    fn project(
        self,
        span: Span<BytePos>,
        symbols: &mut Symbols,
        p: &str,
    ) -> SpannedExpr<'ast, Symbol> {
        p.split('.')
            .fold(None, |acc, name| {
                let symbol = symbols.simple_symbol(name);
                Some(match acc {
                    Some(expr) => pos::spanned(
                        span,
                        Expr::Projection(self.alloc(expr), symbol, Type::hole()),
                    ),
                    None => ident(span, symbol),
                })
            })
            .unwrap()
    }

    fn paren(
        self,
        span: Span<BytePos>,
        expr: SpannedExpr<'ast, Symbol>,
    ) -> SpannedExpr<'ast, Symbol> {
        pos::spanned(
            span,
            Expr::Tuple {
                elems: self.alloc_extend(Some(expr)),
                typ: Type::hole(),
            },
        )
    }

    fn app(
        self,
        span: Span<BytePos>,
        func: Symbol,
        args: impl IntoIterator<Item = SpannedExpr<'ast, Symbol>>,
    ) -> SpannedExpr<'ast, Symbol> {
        let func = pos::spanned(span, Expr::Ident(TypedIdent::new(func)));
        let args = self.alloc_extend(args);
        if args.is_empty() {
            func
        } else {
            pos::spanned(
                span,
                Expr::App {
                    func: self.alloc(func),
                    implicit_args: &mut [],
                    args,
                },
            )
        }
    }

    fn infix(
        self,
        span: Span<BytePos>,
        lhs: SpannedExpr<'ast, Symbol>,
        op: Symbol,
        rhs: SpannedExpr<'ast, Symbol>,
    ) -> SpannedExpr<'ast, Symbol> {
        pos::spanned(
            span,
            Expr::Infix {
                lhs: self.alloc(lhs),
                op: pos::spanned(span, TypedIdent::new(op)),
                rhs: self.alloc(rhs),
                implicit_args: &mut [],
            },
        )
    }
}

fn ident<'ast>(span: Span<BytePos>, s: Symbol) -> SpannedExpr<'ast, Symbol> {
    pos::spanned(span, Expr::Ident(TypedIdent::new(s)))
}

fn literal<'ast>(span: Span<BytePos>, s: &str) -> SpannedExpr<'ast, Symbol> {
    pos::spanned(span, Expr::Literal(Literal::String(s.to_string())))
}

fn is_self_type(self_: &Symbol, typ: &AstType<Symbol>) -> bool {
    match **typ {
        Type::App(ref f, _) => is_self_type(self_, f),
        Type::Alias(ref alias) => alias.name == *self_,
        Type::Ident(ref id) => id.name == *self_,
        _ => false,
    }
}

fn binding_type<'ast>(
    arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    span: Span<BytePos>,
    derive_type_name: &str,
    self_type: AstType<'ast, Symbol>,
    bind: &TypeBinding<'ast, Symbol>,
) -> AstType<'ast, Symbol> {
    let derive_symbol = symbols.simple_symbol(derive_type_name);
    let derive_type = move || arena.clone().ident(KindedIdent::new(derive_symbol.clone()));
    let mut typ = arena.clone().function_implicit(
        bind.alias.value.params().iter().cloned().map(|g| {
            TypeContext::app(
                &mut arena.clone(),
                derive_type(),
                arena.clone().alloc_extend(Some(arena.clone().generic(g))),
            )
        }),
        TypeContext::app(
            &mut arena.clone(),
            derive_type(),
            arena.clone().alloc_extend(Some(self_type)),
        ),
    );

    crate::base::types::walk_type_mut(&mut typ, &mut |typ: &mut AstType<_>| {
        *typ.span_mut() = span;
    });

    typ
}
