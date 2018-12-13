use std::{iter, ops};

use codespan::{ByteOffset, RawOffset};
use itertools::{Either, Itertools};
use pretty::{Arena, Doc, DocAllocator, DocBuilder};

use self::types::pretty_print as pretty_types;
use base::ast::{
    Do, Expr, Literal, Pattern, SpannedExpr, SpannedPattern, ValueBinding, ValueBindings,
};
use base::kind::Kind;
use base::metadata::Attribute;
use base::pos::{self, BytePos, HasSpan, Span, Spanned};
use base::source;
use base::types::{self, ArgType, Prec, Type};

const INDENT: usize = 4;

macro_rules! newlines_iter {
    ($self_:ident, $iterable:expr) => {
        $iterable
            .into_iter()
            .tuple_windows()
            .map(|(prev, next)| $self_.comments(Span::new(prev.end(), next.start())))
    };
}

macro_rules! rev_newlines_iter {
    ($self_:ident, $iterable:expr) => {
        $iterable
            .into_iter()
            .tuple_windows()
            .map(|(prev, next)| $self_.rev_comments(Span::new(prev.end(), next.start())))
    };
}

fn is_newline<'a, A>(doc: &DocBuilder<'a, Arena<'a, A>, A>) -> bool {
    if let Doc::Newline = doc.1 {
        true
    } else {
        false
    }
}

fn is_nil<'a, A>(doc: &DocBuilder<'a, Arena<'a, A>, A>) -> bool {
    if let Doc::Nil = doc.1 {
        true
    } else {
        false
    }
}

pub(super) struct Printer<'a, I: 'a, A: 'a> {
    printer: pretty_types::Printer<'a, I, A>,
    formatter: ::Formatter,
}

impl<'a, I, A> Printer<'a, I, A>
where
    I: AsRef<str>,
{
    pub(super) fn new(
        arena: &'a Arena<'a, A>,
        source: &'a source::Source,
        formatter: ::Formatter,
    ) -> Self {
        Printer {
            printer: pretty_types::Printer::new(arena, source),
            formatter,
        }
    }

    pub(super) fn format(&self, width: usize, newline: &'a str, expr: &'a SpannedExpr<I>) -> String
    where
        A: Clone,
    {
        self.pretty_expr(expr)
            .1
            .pretty(width)
            .to_string()
            .lines()
            .map(|s| format!("{}{}", s.trim_right(), newline))
            .collect()
    }

    fn pretty_expr(&self, expr: &'a SpannedExpr<I>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        self.pretty_expr_with_shebang_line(expr)
            .append(self.comments(Span::new(expr.span.end(), self.source.span().end())))
    }

    fn pretty_expr_with_shebang_line(
        &self,
        expr: &'a SpannedExpr<I>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let start = self.source.span().start();
        let arena = self.arena;
        match self.find_shebang_line() {
            Some(shebang_line) => arena.text(shebang_line).append(self.pretty_expr_(
                start + ByteOffset::from(shebang_line.len() as RawOffset),
                expr,
            )),
            None => self.pretty_expr_(start, expr),
        }
    }

    fn find_shebang_line(&self) -> Option<&'a str> {
        let src = self.source.src();
        if src.starts_with("#!") {
            src.lines().next()
        } else {
            None
        }
    }

    fn pretty_expr_(
        &self,
        previous_end: BytePos,
        mut expr: &'a SpannedExpr<I>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        if !self.formatter.expanded {
            while expr.span.start() == 0.into() {
                expr = match expr.value {
                    Expr::TypeBindings(_, ref expr) | Expr::LetBindings(_, ref expr) => expr,
                    _ => expr,
                };
            }
        }

        let arena = self.arena;

        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start(), next);

        let comments = self.comments(Span::new(previous_end, expr.span.start()));
        let doc = match expr.value {
            Expr::App {
                ref implicit_args,
                ref func,
                ref args,
            } => {
                let arg_iter = iter::once((&**func, false))
                    .chain(implicit_args.iter().map(|arg| (arg, true)))
                    .chain(args.iter().map(|arg| (arg, false)))
                    .tuple_windows()
                    .map(|((prev, _), (arg, implicit))| {
                        self.space(Span::new(prev.span.end(), arg.span.start()))
                            .append(if implicit {
                                arena.text("?")
                            } else {
                                arena.nil()
                            })
                            .append(pretty(arg))
                    });
                pretty(func)
                    .append(arena.concat(arg_iter).nest(INDENT))
                    .group()
            }

            Expr::Array(ref array) => arena
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
                .group(),

            Expr::Block(ref elems) => {
                if elems.len() == 1 {
                    chain![arena;
                        "(",
                        pretty(&elems[0]),
                        ")"
                    ]
                } else {
                    arena.concat(elems.iter().enumerate().map(|(i, elem)| {
                        if i + 1 == elems.len() {
                            pretty(elem).group()
                        } else {
                            pretty(elem)
                                .group()
                                .append(self.comments_after(elem.span.end()))
                        }
                    }))
                }
            }

            Expr::Ident(ref id) => pretty_types::ident(arena, id.name.as_ref()),

            Expr::IfElse(ref body, ref if_true, ref if_false) => {
                let space = newline(arena, expr);
                chain![arena;
                    chain![arena;
                        "if ",
                        pretty(body),
                        arena.space(),
                        "then"
                    ].group(),
                    space.clone().append(pretty(if_true)).nest(INDENT).group(),
                    space.clone(),
                    "else",
                    self.pretty_else_expr(space, if_false)
                ]
            }

            Expr::Infix {
                ref lhs,
                ref op,
                ref rhs,
                ..
            } => chain![arena;
                pretty(lhs).group(),
                chain![arena;
                    newline(arena, rhs),
                    op.value.name.as_ref(),
                    " ",
                    pretty(rhs).group()
                ].nest(INDENT)
            ],

            Expr::Lambda(_) => {
                let (arguments, body) = self.pretty_lambda(previous_end, expr);
                arguments.group().append(body)
            }

            Expr::LetBindings(ref binds, ref body) => {
                let binding = |bind: &'a ValueBinding<I>| {
                    let decl = chain![arena;
                        "let ",
                        chain![arena;
                            self.pretty_pattern(&bind.name),
                            " ",
                            arena.concat(bind.args.iter().map(|arg| {
                                chain![
                                    arena;
                                    if arg.arg_type == ArgType::Implicit {
                                        arena.text("?")
                                    } else {
                                        arena.nil()
                                    },
                                    arena.text(arg.name.value.name.as_ref()).append(" ")
                                ]
                            }))
                        ].group(),
                        match bind.typ {
                            None => arena.nil(),
                            Some(ref typ) => arena.text(": ")
                                .append(types::pretty_print(self, typ))
                                .append(self.space_after(typ.span().end()))
                                .nest(INDENT),
                        },
                        "="
                    ];
                    chain![arena;
                        pretty_types::doc_comment(arena, bind.metadata.comment.as_ref()),
                        self.pretty_attributes(&bind.metadata.attributes),
                        self.hang(decl, &bind.expr).group(),
                        if self.formatter.expanded {
                            arena.newline()
                        } else {
                            arena.nil()
                        }
                    ]
                };
                let is_recursive = match binds {
                    ValueBindings::Recursive(_) => true,
                    ValueBindings::Plain(_) => false,
                };
                chain![arena;
                    if is_recursive {
                        arena.text("rec").append(if binds.len() == 1 { arena.space() } else { arena.newline() })
                    } else {
                        arena.nil()
                    },
                    arena.concat(
                        binds.iter()
                            .map(|bind| binding(bind))
                            .interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))
                    ),
                    if is_recursive {
                        match body.value {
                            Expr::LetBindings(..) => arena.newline().append(arena.text("in")),
                            _ => arena.nil()
                        }
                    } else {
                        arena.nil()
                    },
                    self.pretty_expr_(binds.last().unwrap().span().end(), body).group()
                ]
            }

            Expr::Literal(ref literal) => {
                let text = self.source.src_slice(expr.span);
                let literally = text.starts_with('"')
                    || text.starts_with('\'')
                    || text.starts_with(|c: char| c.is_digit(10))
                    || text.starts_with('-')
                    || text.starts_with("r\"")
                    || text.starts_with("r#");
                if literally {
                    arena.text(text)
                } else {
                    match *literal {
                        Literal::Byte(b) => arena.text(b.to_string()),
                        Literal::Int(i) => arena.text(i.to_string()),
                        Literal::Float(f) => arena.text(f.to_string()),
                        Literal::String(ref s) => chain![arena;
                            "\"",
                            arena.text(&s[..]),
                            "\""
                        ],
                        Literal::Char(c) => chain![arena;
                            "'",
                            arena.text(c.to_string()),
                            "'"
                        ],
                    }
                }
            }

            Expr::Match(ref expr, ref alts) => chain![arena;
                chain![arena;
                    "match ",
                    pretty(expr),
                    " with"
                ].group(),
                arena.newline(),
                arena.concat(alts.iter().map(|alt| {
                    chain![arena;
                        "| ",
                        self.pretty_pattern(&alt.pattern),
                        " ->",
                        self.hang(arena.nil(), &alt.expr).group()
                    ]
                }).intersperse(arena.newline()))
            ],

            Expr::Projection(ref expr, ref field, _) => chain![arena;
                pretty(expr),
                ".",
                pretty_types::ident(arena, field.as_ref())
            ],

            Expr::Record { .. } => {
                let (x, y) = self.pretty_lambda(previous_end, expr);
                x.append(y).group()
            }

            Expr::Tuple { ref elems, .. } => chain![arena;
                "(",
                arena.concat(
                    self.comma_sep_paren(
                    elems
                        .iter()
                        .map(|elem| pos::spanned(elem.span, pretty(elem))),
                    |spanned| spanned.value,
                    ),
                ),
                ")"
            ]
            .group(),

            Expr::TypeBindings(ref binds, ref body) => {
                let is_recursive = binds.len() > 1;

                chain![arena;
                    if is_recursive && binds.len() != 1 {
                        arena.text("rec").append(arena.newline())
                    } else {
                        arena.nil()
                    },

                    pretty_types::doc_comment(arena, binds.first().unwrap().metadata.comment.as_ref()),
                    self.pretty_attributes(&binds.first().unwrap().metadata.attributes),

                    if is_recursive && binds.len() == 1 {
                        arena.text("rec").append(arena.space())
                    } else {
                        arena.nil()
                    },

                    arena.concat(binds.iter().enumerate().map(|(i, bind)| {
                        let typ = bind.alias.value.unresolved_type();
                        let typ = match **typ {
                            // Remove the "parameters"
                            Type::Forall(_, ref typ, _) => typ,
                            _ => typ
                        };
                        let mut type_doc = types::pretty_print(self, typ);
                        match **typ {
                            Type::Record(_) | Type::Variant(_) => (),
                            _ => type_doc = type_doc.nest(INDENT),
                        }
                        chain![arena;
                            if i != 0 {
                                chain![arena;
                                    pretty_types::doc_comment(arena, bind.metadata.comment.as_ref()),
                                    self.pretty_attributes(&bind.metadata.attributes)
                                ]
                            } else {
                                arena.nil()
                            },

                            "type",
                            " ",
                            bind.name.value.as_ref(),
                            " ",
                            arena.concat(bind.alias.value.params().iter().map(|arg| {
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
                            match **typ {
                                Type::Variant(_) => {
                                    chain![arena;
                                        "=",
                                        arena.newline(),
                                        type_doc
                                    ].nest(INDENT)
                                }
                                _ => {
                                    chain![arena;
                                        "= ",
                                        type_doc
                                    ].group()
                                }
                            }
                        ].group()
                    }).interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))),
                    if is_recursive {
                        arena.newline().append(arena.text("in"))
                    } else {
                        arena.nil()
                    },
                    if self.formatter.expanded {
                        arena.newline()
                    } else {
                        arena.nil()
                    },
                    self.pretty_expr_(binds.last().unwrap().alias.span.end(), body)
                ].group()
            }

            Expr::Do(Do {
                ref id,
                ref bound,
                ref body,
                ..
            }) => chain![arena;
                chain![arena;
                    "do",
                    self.space_before(id.span.start()),
                    id.value.name.as_ref(),
                    self.space_after(id.span.end()),
                    "=",
                    self.hang(arena.nil(), bound).group()
                ].group(),
                self.pretty_expr_(bound.span.end(), body)
            ],
            Expr::MacroExpansion { ref original, .. } => {
                return self.pretty_expr_(previous_end, original);
            }
            Expr::Annotated(ref expr, ref typ) => chain![
                arena;
                pretty(expr).group(),
                arena.space(),
                ":",
                arena.space(),
                types::pretty_print(self, typ)
            ],
            Expr::Error(_) => arena.text("<error>"),
        };
        comments.append(doc)
    }

    fn space(&self, span: Span<BytePos>) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.whitespace(span, self.arena.space())
    }

    fn whitespace(
        &self,
        span: Span<BytePos>,
        default: DocBuilder<'a, Arena<'a, A>, A>,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;
        let (doc, count, ends_with_newline) = self.comments_count(span);
        if let Doc::Nil = doc.1 {
            default
        } else if count == 0 {
            // No comments, only newlines from the iterator
            doc
        } else if ends_with_newline {
            arena.space().append(doc)
        } else {
            arena.space().append(doc).append(arena.space())
        }
    }

    fn pretty_else_expr(
        &self,
        space: DocBuilder<'a, Arena<'a, A>, A>,
        if_false: &'a SpannedExpr<I>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start(), next);
        let arena = self.arena;
        match if_false.value {
            Expr::IfElse(ref body, ref if_true, ref if_false) => chain![arena;
                chain![arena;
                    " if ",
                    pretty(body),
                    arena.space(),
                    "then"
                ].group(),
                space.clone().append(pretty(if_true)).nest(INDENT).group(),
                space.clone(),
                "else",
                self.pretty_else_expr(space, if_false)
            ],
            _ => space.append(pretty(if_false)).nest(INDENT).group(),
        }
    }

    fn pretty_lambda(
        &self,
        previous_end: BytePos,
        expr: &'a SpannedExpr<I>,
    ) -> (
        DocBuilder<'a, Arena<'a, A>, A>,
        DocBuilder<'a, Arena<'a, A>, A>,
    )
    where
        A: Clone,
    {
        let arena = self.arena;
        match expr.value {
            Expr::Lambda(ref lambda) => {
                let decl = chain![arena;
                    "\\",
                    arena.concat(lambda.args.iter().map(|arg| {
                        arena.text(arg.name.value.name.as_ref()).append(" ")
                    })),
                    "->"
                ];
                let (next_lambda, body) =
                    self.pretty_lambda(lambda.body.span.start(), &lambda.body);
                if let Doc::Nil = next_lambda.1 {
                    let decl = decl.append(self.space_before(lambda.body.span.start()));
                    (decl, body)
                } else {
                    (decl.append(arena.space()).append(next_lambda), body)
                }
            }
            Expr::Record {
                ref types,
                ref exprs,
                ref base,
                ..
            } => {
                let ordered_iter = || expr.value.field_iter();
                let spans = || {
                    ordered_iter().map(|x| {
                        x.either(
                            |l| l.name.span,
                            |r| {
                                Span::new(
                                    r.name.span.start(),
                                    r.value
                                        .as_ref()
                                        .map_or(r.name.span.start(), |expr| expr.span.end()),
                                )
                            },
                        )
                    })
                };

                // Preserve comments before and after the comma
                let newlines = newlines_iter!(self, spans())
                    .zip(rev_newlines_iter!(self, spans()))
                    .collect::<Vec<_>>();

                let mut line = newline(arena, expr);
                // If there are any explicit line breaks then we need put each field on a separate
                // line
                let newline_in_fields = newlines
                    .iter()
                    .any(|&(ref l, ref r)| !is_nil(l) || !is_nil(r));
                let newline_from_doc_comment = expr.value.field_iter().any(|either| {
                    either
                        .either(|f| &f.metadata, |f| &f.metadata)
                        .comment
                        .is_some()
                });
                let newline_in_base = base
                    .as_ref()
                    .map_or(false, |base| !is_nil(&self.space_before(base.span.start())));
                if newline_in_fields || newline_in_base | newline_from_doc_comment {
                    line = arena.newline();
                }

                let last_field_end = spans()
                    .last()
                    .map_or(expr.span.start() + 1.into(), |s| s.end());
                let last_element_end = base.as_ref().map_or(last_field_end, |base| base.span.end());

                let record = arena
                    .concat(self.comma_sep(
                        ordered_iter().map(|either| match either {
                            Either::Left(l) => pos::spanned(
                                l.name.span,
                                pretty_types::ident(arena, l.name.value.as_ref()),
                            ),
                            Either::Right(r) => {
                                let id = pretty_types::ident(arena, r.name.value.as_ref());
                                let doc = chain![
                                    arena;
                                    pretty_types::doc_comment(arena, r.metadata.comment.as_ref()),
                                    match r.value {
                                        Some(ref expr) => {
                                            let x = chain![arena;
                                            id,
                                            self.space_after(r.name.span.end()),
                                            "="
                                        ];
                                            self.hang(x, expr)
                                        }
                                        None => id,
                                    }
                                ];
                                pos::spanned(r.name.span, doc)
                            }
                        }),
                        |spanned| spanned.value,
                    ))
                    .append(
                        if (!exprs.is_empty() || !types.is_empty()) && is_newline(&line) {
                            arena.text(",")
                        } else {
                            arena.nil()
                        },
                    )
                    .append(match *base {
                        Some(ref base) => {
                            let comments = self.comments_after(last_field_end);
                            chain![arena;
                                if let Doc::Nil = comments.1 {
                                    line.clone()
                                } else {
                                    comments
                                },
                                "..",
                                self.space_before(base.span.start()),
                                self.pretty_expr_(base.span.start(), base)
                            ]
                        }
                        None => arena.nil(),
                    })
                    .nest(INDENT)
                    .append(
                        self.whitespace(Span::new(last_element_end, expr.span.end()), line.clone()),
                    )
                    .group()
                    .append("}");
                (arena.text("{"), record)
            }
            _ => (arena.nil(), self.pretty_expr_(previous_end, expr)),
        }
    }

    fn comma_sep<'e, F, J, T, U>(
        &'e self,
        iter: J,
        f: F,
    ) -> CommaSeparated<'a, 'e, F, I, J::IntoIter, U, A>
    where
        F: FnMut(T) -> DocBuilder<'a, Arena<'a, A>, A>,
        J: IntoIterator<Item = T>,
        T: ::std::borrow::Borrow<Spanned<U, BytePos>>,
    {
        CommaSeparated {
            printer: self,
            iter: iter.into_iter().peekable(),
            f,
            i: 0,
            parens: false,
            _marker: ::std::marker::PhantomData,
        }
    }

    fn pretty_attributes<J>(&self, attributes: J) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        J: IntoIterator<Item = &'a Attribute>,
    {
        let arena = self.arena;
        arena.concat(attributes.into_iter().map(|attribute| {
            chain![arena;
                "#[",
                &attribute.name[..],
                match attribute.arguments {
                    Some(ref arguments) => chain![arena;
                        "(",
                        &arguments[..],
                        ")"
                    ],
                    None => arena.nil(),
                },
                "]",
                arena.newline()
            ]
        }))
    }

    fn pretty_pattern(&self, pattern: &'a SpannedPattern<I>) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.pretty_pattern_(pattern, Prec::Top)
    }

    fn pretty_pattern_(
        &self,
        pattern: &'a SpannedPattern<I>,
        prec: Prec,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;
        match pattern.value {
            Pattern::As(ref ident, ref pat) => prec.enclose(
                Prec::Constructor,
                arena,
                chain![arena;
                    ident.value.as_ref(),
                    " @ ",
                    self.pretty_pattern_(pat, Prec::Constructor)
                ],
            ),
            Pattern::Constructor(ref ctor, ref args) => {
                let doc = chain![arena;
                    ctor.as_ref(),
                    arena.concat(args.iter().map(|arg| {
                        arena.text(" ").append(self.pretty_pattern_(arg, Prec::Constructor))
                    }))
                ];
                if args.is_empty() {
                    doc
                } else {
                    prec.enclose(Prec::Constructor, arena, doc)
                }
            }
            Pattern::Ident(ref id) => pretty_types::ident(arena, id.as_ref()),
            Pattern::Record {
                ref fields,
                ref types,
                ref implicit_import,
                ..
            } => {
                let iter = self.comma_sep(
                    types
                        .iter()
                        .map(|field| {
                            pos::spanned(field.name.span, arena.text(field.name.value.as_ref()))
                        })
                        .chain(fields.iter().map(|field| {
                            let doc = chain![arena;
                                pretty_types::ident(arena, field.name.value.as_ref()),
                                match field.value {
                                    Some(ref new_name) => {
                                        chain![arena;
                                            " = ",
                                            self.pretty_pattern(new_name)
                                        ]
                                    }
                                    None => arena.nil(),
                                }
                            ];
                            pos::spanned(field.name.span, doc)
                        }))
                        .chain(
                            implicit_import
                                .as_ref()
                                .map(|spanned| pos::spanned(spanned.span, arena.text("?"))),
                        ),
                    |spanned| spanned.value,
                );
                let doc = arena.concat(iter).nest(INDENT);
                chain![arena;
                    "{",
                    doc,
                    if types.is_empty() && fields.is_empty() && implicit_import.is_none() {
                        arena.nil()
                    } else {
                        arena.space()
                    },
                    "}"
                ]
                .group()
            }
            Pattern::Tuple { ref elems, .. } => chain![arena;
                "(",
                arena.concat(self.comma_sep_paren(
                    elems
                        .iter()
                        .map(|elem| pos::spanned(elem.span, self.pretty_pattern(elem))),
                    |elem| elem.value)
                ),
                ")"
            ]
            .group(),
            Pattern::Error => arena.text("<error>"),
            Pattern::Literal(_) => arena.text(self.source.src_slice(pattern.span)),
        }
    }

    fn hang(
        &self,
        from: DocBuilder<'a, Arena<'a, A>, A>,
        expr: &'a SpannedExpr<I>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let arena = self.arena;
        let (arguments, body) = self.pretty_lambda(expr.span.start(), expr);
        match expr.value {
            Expr::Record { .. } => {
                let opening = arguments;
                let spaces = self.space_before(expr.span.start());
                // If there are just spaces between `=`/`->` and the opening brace (`{`) we hang
                // the opening brace next to the `=` and only indent the body of the record
                // let x = {
                //     y,
                // }
                // Instead of
                // let x =
                //     {
                //         y,
                //     }
                let needs_indent = if let Doc::Space = spaces.1 {
                    false
                } else {
                    true
                };
                let doc = chain![arena;
                    chain![arena;
                        from,
                        spaces,
                        opening
                    ].group(),
                    body
                ]
                .group();
                if needs_indent {
                    doc.nest(INDENT)
                } else {
                    doc
                }
            }
            _ => {
                let mut spaces = self.space_before(expr.span.start());
                if let Doc::Space = spaces.1 {
                    match expr.value {
                        Expr::Lambda(..) => (),
                        _ => spaces = newline(arena, expr),
                    }
                }

                from.append(
                    chain![arena;
                        spaces,
                        arguments
                    ]
                    .group()
                    .append(body)
                    .nest(INDENT),
                )
                .group()
            }
        }
    }

    fn comma_sep_paren<'e, J, F, T, U>(
        &'e self,
        iter: J,
        f: F,
    ) -> CommaSeparated<'a, 'e, F, I, J::IntoIter, U, A>
    where
        F: FnMut(T) -> DocBuilder<'a, Arena<'a, A>, A>,
        J: IntoIterator<Item = T>,
        T: ::std::borrow::Borrow<Spanned<U, BytePos>>,
    {
        CommaSeparated {
            printer: self,
            iter: iter.into_iter().peekable(),
            f,
            i: 0,
            parens: true,
            _marker: ::std::marker::PhantomData,
        }
    }

    fn comments(&self, span: Span<BytePos>) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.comments_count(span).0
    }

    fn rev_comments(&self, span: Span<BytePos>) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;

        if span.start() == 0.into() {
            return arena.nil();
        }

        self.source
            .comments_between(span)
            .rev()
            .map(|comment| {
                if comment.is_empty() {
                    arena.newline()
                } else if comment.starts_with("//") {
                    arena.text(comment).append(arena.newline())
                } else {
                    arena.text(comment)
                }
            })
            .fold(arena.nil(), |acc, doc| doc.append(acc))
    }
}

impl<'a, I, A> ops::Deref for Printer<'a, I, A> {
    type Target = pretty_types::Printer<'a, I, A>;

    fn deref(&self) -> &Self::Target {
        &self.printer
    }
}

struct CommaSeparated<'a: 'e, 'e, F, I, J, U, A>
where
    I: 'a,
    A: 'a,
    J: Iterator,
{
    printer: &'e Printer<'a, I, A>,
    iter: ::std::iter::Peekable<J>,
    f: F,
    parens: bool,
    i: usize,
    _marker: ::std::marker::PhantomData<U>,
}

impl<'a, 'e, F, I, J, T, U, A> Iterator for CommaSeparated<'a, 'e, F, I, J, U, A>
where
    I: AsRef<str>,
    F: FnMut(T) -> DocBuilder<'a, Arena<'a, A>, A>,
    J: Iterator<Item = T>,
    T: ::std::borrow::Borrow<Spanned<U, BytePos>>,
{
    type Item = DocBuilder<'a, Arena<'a, A>, A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|item| {
            let span = item.borrow().span;
            let arena = self.printer.arena;
            let i = self.i;
            self.i += 1;
            chain![arena;
                if i == 0 && self.parens {
                    self.printer.comments_before(span.start())
                } else {
                    self.printer.space_before(span.start())
                },
                (self.f)(item),
                if self.iter.peek().is_some() {
                    self.printer
                        .comments(Span::new(span.end(), self.printer.source.span().end()))
                        .append(",")
                } else {
                    arena.nil()
                }
            ]
        })
    }
}

fn pretty_kind<'a, A>(
    arena: &'a Arena<'a, A>,
    prec: Prec,
    kind: &'a Kind,
) -> DocBuilder<'a, Arena<'a, A>, A> {
    match *kind {
        Kind::Type => arena.text("Type"),
        Kind::Error => arena.text("!"),
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

fn newline<'a, Id, A>(
    arena: &'a Arena<'a, A>,
    expr: &'a SpannedExpr<Id>,
) -> DocBuilder<'a, Arena<'a, A>, A> {
    if forced_new_line(expr) {
        arena.newline()
    } else {
        arena.space()
    }
}

fn forced_new_line<Id>(expr: &SpannedExpr<Id>) -> bool {
    match expr.value {
        Expr::LetBindings(..) | Expr::Match(..) | Expr::TypeBindings(..) | Expr::Do(..) => true,
        Expr::Lambda(ref lambda) => forced_new_line(&lambda.body),
        Expr::Tuple { ref elems, .. } => elems.iter().any(forced_new_line),
        Expr::Record {
            ref exprs,
            ref base,
            ..
        } => exprs.iter().any(|field| {
            field
                .value
                .as_ref()
                .map_or(false, |expr| forced_new_line(expr))
                || base.as_ref().map_or(false, |base| forced_new_line(base))
        }),
        Expr::IfElse(_, ref t, ref f) => forced_new_line(t) || forced_new_line(f),
        Expr::Infix {
            ref lhs, ref rhs, ..
        } => forced_new_line(lhs) || forced_new_line(rhs),
        _ => false,
    }
}
