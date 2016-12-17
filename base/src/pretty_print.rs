use std::iter::repeat;

use itertools::Itertools;
use pretty::{Arena, DocAllocator, DocBuilder};

use ast::{Expr, is_operator_char, Literal, Pattern, SpannedExpr, SpannedPattern};
use pos::{BytePos, Span};
use source::Source;
use types::{Type, pretty_print as pretty_type};

const INDENT: usize = 4;

pub fn ident<'b>(arena: &'b Arena<'b>, name: &'b str) -> DocBuilder<'b, Arena<'b>> {
    if name.starts_with(is_operator_char) {
        chain![arena; "(", name, ")"]
    } else {
        arena.text(name)
    }
}

fn forced_new_line<Id>(expr: &Expr<Id>) -> bool {
    match *expr {
        Expr::Block(..) |
        Expr::LetBindings(..) |
        Expr::Match(..) |
        Expr::TypeBindings(..) => true,
        Expr::Lambda(ref lambda) => forced_new_line(&lambda.body.value),
        _ => false,
    }
}

fn doc_comment<'a>(arena: &'a Arena<'a>, text: &'a Option<String>) -> DocBuilder<'a, Arena<'a>> {
    match *text {
        Some(ref text) => {
            arena.concat(text.lines()
                .map(|line| arena.text("/// ").append(line).append(arena.newline())))
        }
        None => arena.nil(),
    }
}

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
        Pattern::Ident(ref id) => ident(arena, id.as_ref()),
        Pattern::Record {
            ref fields,
            ref types,
            ..
        } => {
            chain![arena;
                "{",
                arena.concat(types.iter().map(|field| {
                    chain![arena;
                        arena.space(),
                        field.0.as_ref()
                    ]
                }).chain(fields.iter().map(|field| {
                    chain![arena;
                        arena.space(),
                        ident(arena, field.0.as_ref()),
                        match field.1 {
                            Some(ref new_name) => {
                                chain![arena;
                                    " = ",
                                    pretty_pattern(arena, new_name)
                                ]
                            }
                            None => arena.nil(),
                        }
                    ]
                })).intersperse(arena.text(","))),
                if types.is_empty() && fields.is_empty() {
                    arena.nil()
                } else {
                    arena.space()
                },
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
        Pattern::Error => arena.text("<error>"),
    }
}

pub struct ExprPrinter<'a> {
    arena: Arena<'a>,
    source: &'a Source<'a>,
}

impl<'a> ExprPrinter<'a> {
    pub fn new(source: &'a Source<'a>) -> ExprPrinter<'a> {
        ExprPrinter {
            arena: Arena::new(),
            source: source,
        }
    }

    pub fn pretty_expr<Id>(&'a self, expr: &'a SpannedExpr<Id>) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        self.pretty_expr_(BytePos::from(0), expr)
    }
    pub fn pretty_expr_<Id>(&'a self,
                            previous_end: BytePos,
                            expr: &'a SpannedExpr<Id>)
                            -> DocBuilder<'a, Arena<'a>>
        where Id: AsRef<str>,
    {
        let arena = &self.arena;

        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start, next);

        let newlines = |prev, next| {
            let prev_line = self.source.line_number_at_byte(prev);
            let next_line = self.source.line_number_at_byte(next);
            arena.concat(
                repeat(arena.newline()).take((next_line - prev_line).to_usize()),
            )
        };
        macro_rules! newlines_iter {
            ($iterable: expr) => {
                $iterable.into_iter().tuple_windows().map(|(prev, next)| newlines(prev.end, next.start))
            }
        }


        let doc = match expr.value {
            Expr::App(ref func, ref args) => {
                pretty(func).append(
                    arena.concat(args.iter().map(|arg| arena.space().append(pretty(arg)))),
                )
            }
            Expr::Array(ref array) => {
                arena
                    .text("[")
                    .append(
                        arena.concat(
                            array
                                .exprs
                                .iter()
                                .map(|elem| pretty(elem))
                                .intersperse(arena.text(",").append(arena.space())),
                        ),
                    )
                    .append("]")
                    .group()
            }
            Expr::Block(ref elems) => {
                if elems.len() == 1 {
                    chain![arena;
                        "(",
                        pretty(&elems[0]),
                        ")"
                    ]
                } else {
                    arena.concat(
                        elems
                            .iter()
                            .map(|elem| pretty(elem).group().append(arena.newline())),
                    )
                }
            }
            Expr::Ident(ref id) => ident(arena, id.name.as_ref()),
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
                    self.hang(&lambda.body)
                ]
            }
            Expr::LetBindings(ref binds, ref body) => {
                chain![arena;
                    doc_comment(arena, &binds.first().unwrap().comment),
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
                                ref typ => arena.text(": ")
                                    .append(pretty_type(arena, typ))
                                    .append(arena.space()),
                            },
                            "=",
                            self.hang(&bind.expr)
                        ].group().nest(INDENT)
                    }).interleave(newlines_iter!(binds.iter().map(|bind| bind.span()))
                        .map(|doc| doc.append("and ")))),
                    newlines(binds.last().unwrap().expr.span.end, body.span.start),
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
                            self.hang(&alt.expr).group().nest(INDENT)
                        ]
                    }).intersperse(arena.newline()))
                ]
            }
            Expr::Projection(ref expr, ref field, _) => {
                chain![arena;
                    pretty(expr),
                    ".",
                    field.as_ref()
                ]
            }
            Expr::Record {
                ref types,
                ref exprs,
                ..
            } => {
                chain![arena;
                    "{",
                    arena.concat(types.iter().map(|field| {
                        chain![arena;
                            arena.space(),
                            field.name.as_ref()
                        ]
                    }).chain(exprs.iter().map(|field| {
                        chain![arena;
                            arena.space(),
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
                            }
                        ]
                    })).intersperse(arena.text(","))).block(INDENT),
                    if types.is_empty() && exprs.is_empty() {
                        arena.nil()
                    } else {
                        arena.space()
                    },
                    "}"
                ].group()
            }
            Expr::Tuple { ref elems, .. } => {
                arena
                    .text("(")
                    .append(
                        arena.concat(
                            elems
                                .iter()
                                .map(|elem| pretty(elem))
                                .intersperse(arena.text(",").append(arena.space())),
                        ),
                    )
                    .append(")")
                    .group()
            }
            Expr::TypeBindings(ref binds, ref body) => {
                chain![arena;
                    doc_comment(arena, &binds.first().unwrap().comment),
                    "type ",
                    arena.concat(binds.iter().map(|bind| {
                        chain![arena;
                            bind.name.value.as_ref(),
                            " ",
                            arena.concat(bind.alias.value.args.iter().map(|arg| {
                                arena.text(arg.id.as_ref()).append(" ")
                            })),
                            "=",
                            arena.space()
                                .append(pretty_type(arena, &bind.alias.value.unresolved_type()))
                                .group()
                        ].group().nest(INDENT)
                    }).interleave(newlines_iter!(binds.iter().map(|bind| bind.span()))
                        .map(|doc| doc.append("and ")))),
                    newlines(binds.last().unwrap().alias.span.end, body.span.start),
                    pretty(body)
                ]
            }
            Expr::Error => arena.text("<error>"),
        };
        arena.concat(self.source
                .comments_between(Span::new(previous_end, expr.span.start))
                .map(|comment| {
                    chain![arena;
                        if comment.is_empty() {
                            arena.nil()
                        } else {
                            arena.text("// ").append(comment)
                        },
                        arena.newline()
                    ]
                }))
            .append(doc)
    }

    fn hang<Id>(&'a self, expr: &'a SpannedExpr<Id>) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        let line = if forced_new_line(&expr.value) {
            self.arena.newline()
        } else {
            self.arena.space()
        };
        line.append(self.pretty_expr(expr))
            .block(INDENT)
    }
}
