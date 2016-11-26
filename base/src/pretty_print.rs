use pretty::{Arena, DocAllocator, DocBuilder};

use ast::{Expr, Literal, Pattern, SpannedExpr, SpannedPattern};
use types::{Type, pretty_print as pretty_type};

const INDENT: usize = 4;

pub fn pretty_pattern<'a, Id>(arena: &'a Arena<'a>,
                              pattern: &'a SpannedPattern<Id>)
                              -> DocBuilder<'a, Arena<'a>>
    where Id: AsRef<str>,
{
    match pattern.value {
        Pattern::Constructor(ref ctor, ref args) => {
            chain![arena;
                ctor.as_ref(),
                arena.concat(args.iter().map(|arg| {
                    arena.text(" ").append(pretty_pattern(arena, arg))
                }))
            ]
        }
        Pattern::Ident(ref id) => arena.text(id.as_ref()),
        Pattern::Record { ref fields, ref types, .. } => {
            chain![arena;
                "{",
                arena.concat(types.iter().map(|field| {
                    chain![arena;
                        field.0.as_ref(),
                        ",",
                        arena.space()
                    ]
                })),
                arena.concat(fields.iter().map(|field| {
                    match field.1 {
                        Some(ref new_name) => {
                            chain![arena;
                                field.0.as_ref(),
                                " = ",
                                pretty_pattern(arena, new_name),
                                ",",
                                arena.space()
                            ]
                        }
                        None => {
                            chain![arena;
                                field.0.as_ref(),
                                ",",
                                arena.space()
                            ]
                        }
                    }
                })),
                "}"
            ]
        }
        Pattern::Tuple { ref elems, .. } => {
            chain![arena;
                "(",
                arena.concat(elems
                    .iter()
                    .map(|elem| pretty_pattern(arena, elem))
                    .intersperse(arena.text(",").append(arena.space()))
                ),
                ")"
            ]
        }
    }
}

pub fn pretty_expr<'a, Id>(arena: &'a Arena<'a>, expr: &'a Expr<Id>) -> DocBuilder<'a, Arena<'a>>
    where Id: AsRef<str>,
{
    let pretty = |expr: &'a SpannedExpr<_>| pretty_expr(arena, &expr.value);
    match *expr {
        Expr::App(ref func, ref args) => {
            pretty(func)
                .append(arena.concat(args.iter().map(|arg| arena.text(" ").append(pretty(arg)))))
        }
        Expr::Array(ref array) => {
            arena.text("[")
                .append(arena.concat(array.exprs.iter().map(|elem| pretty(elem).append(", "))))
                .append("]")
                .group()
        }
        Expr::Block(ref elems) => {
            arena.concat(elems.iter().map(|elem| pretty(elem).append(arena.newline())))
        }
        Expr::Ident(ref id) => arena.text(id.name.as_ref()),
        Expr::IfElse(ref body, ref if_true, ref if_false) => {
            chain![arena;
                "if",
                pretty(body),
                "then",
                pretty(if_true),
                "else",
                pretty(if_false)
            ]
        }
        Expr::Infix(ref l, ref op, ref r) => {
            chain![arena;
                pretty(l),
                " ",
                op.value.name.as_ref(),
                " ",
                pretty(r)
            ]
        }
        Expr::Lambda(ref lambda) => {
            chain![arena;
                "\\",
                arena.concat(lambda.args.iter().map(|arg| arena.text(arg.name.as_ref()).append(" "))),
                "->",
                pretty(&lambda.body)
            ]
        }
        Expr::LetBindings(ref binds, ref body) => {
            chain![arena;
                "let ",
                arena.concat(binds.iter().map(|bind| {
                    chain![arena;
                        chain![arena;
                            pretty_pattern(arena, &bind.name),
                            " ",
                            arena.concat(bind.args.iter().map(|arg| {
                                arena.text(arg.name.as_ref()).append(" ")
                            }))
                        ].group(),
                        match *bind.typ {
                            Type::Hole => arena.nil(),
                            ref typ => arena.text(": ").append(pretty_type(arena, typ)),
                        },
                        "=",
                        arena.space()
                            .append(pretty(&bind.expr))
                            .group(),
                        arena.newline()
                    ].group().nest(INDENT)
                })),
                "in",
                arena.space(),
                pretty(body)
            ]
        }
        Expr::Literal(ref literal) => {
            match *literal {
                Literal::Byte(b) => arena.text(format!("b{}", b)),
                Literal::Char(c) => arena.text(format!("{:?}", c)),
                Literal::Float(f) => arena.text(format!("{}", f)),
                Literal::Int(i) => arena.text(format!("{}", i)),
                Literal::String(ref s) => arena.text(format!("{:?}", s)),
            }
        }
        Expr::Match(ref expr, ref alts) => {
            chain![arena;
                "match ",
                pretty(expr),
                " with",
                arena.newline(),
                arena.concat(alts.iter().map(|alt| {
                    chain![arena;
                        "| ",
                        pretty_pattern(arena, &alt.pattern),
                        " ->",
                        arena.space(),
                        pretty(&alt.expr).group().nest(INDENT),
                        arena.newline()
                    ]
                }))
            ]
        }
        Expr::Projection(ref expr, ref field, _) => {
            chain![arena;
                pretty(expr),
                ".",
                field.as_ref()
            ]
        }
        Expr::Record { ref types, ref exprs, .. } => {
            chain![arena;
                "{",
                arena.concat(types.iter().map(|field| {
                    chain![arena;
                        field.name.as_ref(),
                        ",",
                        arena.space()
                    ]
                })),
                arena.concat(exprs.iter().map(|field| {
                    chain![arena;
                        field.name.as_ref(),
                        match field.value {
                            Some(ref expr) => {
                                chain![arena;
                                    " =",
                                    arena.space(),
                                    pretty(&expr)
                                ]
                            },
                            None => arena.nil(),
                        },
                        ",",
                        arena.space()
                    ]
                })),
                "}"
            ]
        }
        Expr::Tuple{ ref elems, .. } => {
            arena.text("(")
                .append(arena.concat(elems.iter().map(|elem| pretty(elem).append(", "))))
                .append(")")
                .group()
        }
        Expr::TypeBindings(ref binds, ref body) => {
            chain![arena;
                "type ",
                arena.concat(binds.iter().map(|bind| {
                    chain![arena;
                        bind.name.as_ref(),
                        " ",
                        arena.concat(bind.alias.args.iter().map(|arg| {
                            arena.text(arg.id.as_ref()).append(" ")
                        })),
                        "=",
                        arena.space()
                            .append(pretty_type(arena, &bind.alias.unresolved_type()))
                            .group(),
                        arena.newline()
                            .append(pretty_type(arena, &bind.alias.unresolved_type()))
                    ].group().nest(INDENT)
                })),
                arena.space(),
                "in",
                arena.space(),
                pretty(body)
            ]
        }
        Expr::Error => arena.text("<error expr>"),
    }
}
