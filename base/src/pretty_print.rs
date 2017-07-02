use std::iter::{once, repeat};

use itertools::{Either, Itertools};
use pretty::{Arena, DocAllocator, DocBuilder};

use ast::{Expr, Comment, CommentType, is_operator_char, Pattern, SpannedExpr,
          SpannedPattern, ValueBinding};
use kind::Kind;
use pos::{BytePos, Line, Span};
use source::Source;
use types::{Prec, Type, pretty_print as pretty_type};

const INDENT: usize = 4;

pub fn ident<'b>(arena: &'b Arena<'b>, name: &'b str) -> DocBuilder<'b, Arena<'b>> {
    if name.starts_with(is_operator_char) {
        chain![arena; "(", name, ")"]
    } else {
        arena.text(name)
    }
}

fn forced_new_line<Id>(expr: &SpannedExpr<Id>) -> bool {
    match expr.value {
        Expr::LetBindings(..) |
        Expr::Match(..) |
        Expr::TypeBindings(..) => true,
        Expr::Lambda(ref lambda) => forced_new_line(&lambda.body),
        Expr::Tuple { ref elems, .. } => elems.iter().any(forced_new_line),
        Expr::Record { ref exprs, .. } => {
            exprs.iter().any(|field| {
                field
                    .value
                    .as_ref()
                    .map_or(false, |expr| forced_new_line(expr))
            })
        }
        Expr::IfElse(_, ref t, ref f) => forced_new_line(t) || forced_new_line(f),
        Expr::Infix(ref l, _, ref r) => forced_new_line(l) || forced_new_line(r),
        _ => false,
    }
}
fn newline<'a, Id>(arena: &'a Arena<'a>, expr: &'a SpannedExpr<Id>) -> DocBuilder<'a, Arena<'a>> {
    if forced_new_line(expr) {
        arena.newline()
    } else {
        arena.space()
    }
}

fn doc_comment<'a>(arena: &'a Arena<'a>, text: &'a Option<Comment>) -> DocBuilder<'a, Arena<'a>> {
    match *text {
        Some(ref comment) => {
            match comment.typ {
                CommentType::Line => {
                    arena.concat(comment.content.lines().map(|line| {
                        arena.text("/// ").append(line).append(arena.newline())
                    }))
                }
                CommentType::Block => {
                    chain![arena;
                        "/**",
                        arena.newline(),
                        arena.concat(comment.content.lines().map(|line| {
                            arena.text(line).append(arena.newline())
                        })),
                        "*/",
                        arena.newline()
                    ]
                }
            }
        }
        None => arena.nil(),
    }
}

pub fn pretty_kind<'a>(
    arena: &'a Arena<'a>,
    prec: Prec,
    kind: &'a Kind,
) -> DocBuilder<'a, Arena<'a>> {
    match *kind {
        Kind::Type => arena.text("Type"),
        Kind::Row => arena.text("Row"),
        Kind::Hole => arena.text("_"),
        Kind::Variable(ref id) => arena.text(id.to_string()),
        Kind::Function(ref a, ref r) => {
            let doc = chain![arena;
                pretty_kind(arena, Prec::Function, a),
                arena.space(),
                "-> ",
                pretty_kind(arena, Prec::Top, r)
            ];
            prec.enclose(Prec::Function, arena, doc)
        }
    }
}
pub fn pretty_pattern<'a, Id>(
    arena: &'a Arena<'a>,
    pattern: &'a SpannedPattern<Id>,
) -> DocBuilder<'a, Arena<'a>>
where
    Id: AsRef<str>,
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
                        field.name.value.as_ref()
                    ]
                }).chain(fields.iter().map(|field| {
                    chain![arena;
                        arena.space(),
                        ident(arena, field.name.value.as_ref()),
                        match field.value {
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
            ].group()
        }
        Pattern::Error => arena.text("<error>"),
    }
}

macro_rules! newlines_iter {
    ($self_: ident, $iterable: expr) => {
        $iterable.into_iter().tuple_windows().map(|(prev, next)| $self_.newlines(prev.end, next.start))
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

    pub fn format<Id>(&'a self, width: usize, newline: &'a str, expr: &'a SpannedExpr<Id>) -> String
    where
        Id: AsRef<str>,
    {
        self.pretty_expr(expr)
            .1
            .pretty(width)
            .to_string()
            .lines()
            .map(|s| format!("{}{}", s.trim_right(), newline))
            .collect()
    }


    fn newlines(&'a self, prev: BytePos, next: BytePos) -> DocBuilder<'a, Arena<'a>> {
        let arena = &self.arena;
        let prev_line = self.source.line_number_at_byte(prev);
        let next_line = self.source.line_number_at_byte(next);
        // Record expressions
        let empty_lines = (prev_line.to_usize()..next_line.to_usize())
            .map(|l| {
                self.source.line(Line::from(l)).unwrap().1.trim().is_empty()
            })
            .count();
        arena.concat(repeat(arena.newline()).take(empty_lines))
    }

    pub fn pretty_expr<Id>(&'a self, expr: &'a SpannedExpr<Id>) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        self.pretty_expr_(BytePos::from(0), expr)
    }
    pub fn pretty_expr_<Id>(
        &'a self,
        previous_end: BytePos,
        expr: &'a SpannedExpr<Id>,
    ) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        let arena = &self.arena;

        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start, next);

        let doc = match expr.value {
            Expr::App(ref func, ref args) => {
                pretty(func)
                    .append(
                        arena
                            .concat(args.iter().map(|arg| arena.space().append(pretty(arg))))
                            .nest(INDENT),
                    )
                    .group()
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
                            .map(|elem| pretty(elem).group())
                            .intersperse(arena.newline()),
                    )
                }
            }
            Expr::Ident(ref id) => ident(arena, id.name.as_ref()),
            Expr::IfElse(ref body, ref if_true, ref if_false) => {
                let space = newline(arena, expr);
                chain![arena;
                    arena.text("if ").append(pretty(body)).group(),
                    arena.space(),
                    "then",
                    space.clone().append(pretty(if_true)).nest(INDENT).group(),
                    space.clone(),
                    "else",
                    space.append(pretty(if_false)).nest(INDENT).group()
                ]
            }
            Expr::Infix(ref l, ref op, ref r) => {
                chain![arena;
                    pretty(l).group(),
                    chain![arena;
                        newline(arena, r),
                        op.value.name.as_ref(),
                        " ",
                        pretty(r).group()
                    ].nest(INDENT)
                ]
            }
            Expr::Lambda(_) => {
                let (arguments, body) = self.pretty_lambda(previous_end, expr);
                arguments.group().append(body)
            }
            Expr::LetBindings(ref binds, ref body) => {
                let binding = |prefix: &'a str, bind: &'a ValueBinding<Id>| {
                    let decl = chain![arena;
                        prefix,
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
                        "="
                    ];
                    chain![arena;
                        doc_comment(arena, &bind.comment),
                        self.hang(decl, &bind.expr).group()
                    ]
                };
                let prefixes = once("let ").chain(repeat("and "));
                chain![arena;
                    arena.concat(prefixes.zip(binds).map(|(prefix, bind)| {
                        binding(prefix, bind)
                    }).interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))),
                    self.newlines(binds.last().unwrap().expr.span.end, body.span.start),
                    pretty(body).group()
                ]
            }
            Expr::Literal(_) => {
                arena.text(
                    &self.source.src()[expr.span.start.to_usize()..expr.span.end.to_usize()],
                )
            }
            Expr::Match(ref expr, ref alts) => {
                chain![arena;
                    chain![arena;
                        "match ",
                        pretty(expr),
                        " with"
                    ].group(),
                    arena.newline(),
                    arena.concat(alts.iter().map(|alt| {
                        chain![arena;
                            "| ",
                            pretty_pattern(arena, &alt.pattern),
                            " ->",
                            self.hang(arena.nil(), &alt.expr).group()
                        ]
                    }).intersperse(arena.newline()))
                ]
            }
            Expr::Projection(ref expr, ref field, _) => {
                chain![arena;
                    pretty(expr),
                    ".",
                    ident(arena, field.as_ref())
                ]
            }
            Expr::Record { .. } => {
                let (x, y) = self.pretty_lambda(previous_end, expr);
                x.append(y).group()
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
                let prefixes = once("type").chain(repeat("and"));
                chain![arena;
                    doc_comment(arena, &binds.first().unwrap().comment),
                    arena.concat(binds.iter().zip(prefixes).map(|(bind, prefix)| {
                        let mut type_doc = pretty_type(arena, &bind.alias.value.unresolved_type());
                        match **bind.alias.value.unresolved_type() {
                            Type::Record(_) => (),
                            _ => type_doc = type_doc.nest(INDENT),
                        }
                        chain![arena;
                            prefix,
                            " ",
                            bind.name.value.as_ref(),
                            " ",
                            arena.concat(bind.alias.value.args.iter().map(|arg| {
                                chain![arena;
                                    if *arg.kind != Kind::Type && *arg.kind != Kind::Hole {
                                        chain![arena;
                                            "(",
                                            arg.id.as_ref(),
                                            " :",
                                            arena.space(),
                                            pretty_kind(arena, Prec::Top, &arg.kind).group(),
                                            ")"
                                        ].group()
                                    } else {
                                        arena.text(arg.id.as_ref())
                                    },
                                    arena.space()
                                ]
                            })).group(),
                            arena.text("= ")
                                .append(type_doc)
                                .group()
                        ].group()
                    }).interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))),
                    self.newlines(binds.last().unwrap().alias.span.end, body.span.start),
                    pretty(body)
                ].group()
            }
            Expr::Error => arena.text("<error>"),
        };
        arena
            .concat(
                self.source
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
                    }),
            )
            .append(doc)
    }

    fn pretty_lambda<Id>(
        &'a self,
        previous_end: BytePos,
        expr: &'a SpannedExpr<Id>,
    ) -> (DocBuilder<'a, Arena<'a>>, DocBuilder<'a, Arena<'a>>)
    where
        Id: AsRef<str>,
    {
        let arena = &self.arena;
        match expr.value {
            Expr::Lambda(ref lambda) => {
                let decl = chain![arena;
                    "\\",
                    arena.concat(lambda.args.iter().map(|arg| arena.text(arg.name.as_ref()).append(" "))),
                    "->"
                ];
                let (next_lambda, body) = self.pretty_lambda(previous_end, &lambda.body);
                if next_lambda.1 == arena.nil().1 {
                    (decl, body)
                } else {
                    (decl.append(arena.space()).append(next_lambda), body)
                }
            }
            Expr::Record {
                ref types,
                ref exprs,
                ..
            } => {
                let ordered_iter = || {
                    types.iter().map(Either::Left).merge_by(
                        exprs.iter().map(Either::Right),
                        |x, y| {
                            x.either(|l| l.name.span.start, |r| r.name.span.start) <
                                y.either(|l| l.name.span.start, |r| r.name.span.start)
                        },
                    )
                };

                let newlines = newlines_iter!(
                    self,
                    ordered_iter().map(|x| {
                        x.either(|l| l.name.span, |r| {
                            Span::new(
                                r.name.span.start,
                                r.value
                                    .as_ref()
                                    .map_or(r.name.span.start, |expr| expr.span.end),
                            )
                        })
                    })
                ).collect::<Vec<_>>();

                let mut line = newline(arena, expr);
                // If there are any explicit line breaks then we need put each field on a separate line
                if newlines.iter().any(|doc| doc.1 != arena.nil().1) {
                    line = arena.newline();
                }
                let end_iter = newlines.into_iter().map(|mut doc| {
                    if doc.1 == arena.nil().1 {
                        doc = line.clone();
                    }
                    arena.text(",").append(doc)
                });

                let record = chain![arena;
                    if types.is_empty() && exprs.is_empty() {
                        arena.nil()
                    } else {
                        line.clone()
                    },
                    arena.concat(ordered_iter().map(|either| {
                        match either {
                            Either::Left(l) => {
                                ident(arena, l.name.value.as_ref())
                            }
                            Either::Right(r) => {
                                let id = ident(arena, r.name.value.as_ref());
                                match r.value {
                                    Some(ref expr) => self.hang(id.append(" ="), expr),
                                    None => id,
                                }
                            }
                        }
                    }).interleave(end_iter))
                ].nest(INDENT)
                    .append(line.clone())
                    .group()
                    .append("}");
                (arena.text("{"), record)
            }
            _ => (arena.nil(), self.spaced_pretty_expr(previous_end, expr)),
        }
    }

    fn hang<Id>(
        &'a self,
        from: DocBuilder<'a, Arena<'a>>,
        expr: &'a SpannedExpr<Id>,
    ) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        let (arguments, mut body) = self.pretty_lambda(expr.span.start, expr);
        let first = if arguments.1 == self.arena.nil().1 {
            self.arena.nil()
        } else {
            self.arena.space()
        };
        match expr.value {
            Expr::Record { .. } => (),
            _ => body = body.nest(INDENT),
        }
        from.append(first)
            .append(arguments)
            .group()
            .append(body)
            .group()
    }

    fn spaced_pretty_expr<Id>(
        &'a self,
        previous_end: BytePos,
        expr: &'a SpannedExpr<Id>,
    ) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        let line = newline(&self.arena, expr);
        line.append(self.pretty_expr_(previous_end, expr))
    }
}
