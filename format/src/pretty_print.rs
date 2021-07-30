use std::{iter, ops};

use {
    codespan::{ByteOffset, RawOffset},
    itertools::{Either, Itertools},
    pretty::{Arena, Doc, DocAllocator, DocBuilder},
};

use self::types::pretty_print as pretty_types;
use base::{
    ast::{
        Do, Expr, Literal, Pattern, PatternField, SpannedExpr, SpannedPattern, ValueBinding,
        ValueBindings,
    },
    kind::Kind,
    metadata::Attribute,
    pos::{self, BytePos, HasSpan, Span, Spanned},
    source,
    types::{self, ArgType, AsId, Prec, Type},
};

const INDENT: isize = 4;

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

fn is_nil<'a, A>(doc: &DocBuilder<'a, Arena<'a, A>, A>) -> bool {
    if let Doc::Nil = *doc.1 {
        true
    } else {
        false
    }
}

fn trailing_comma<'a, A>(arena: &'a Arena<'a, A>) -> DocBuilder<'a, Arena<'a, A>, A> {
    arena.text(",").flat_alt(arena.nil())
}

pub(super) struct Printer<'a, I: 'a, A: 'a> {
    printer: pretty_types::Printer<'a, I, A>,
    formatter: crate::Formatter,
}

impl<'a, I, A> Printer<'a, I, A>
where
    I: AsRef<str> + AsId<I> + std::fmt::Debug + 'a,
    A: std::fmt::Debug,
    A: 'a,
{
    pub(super) fn new(
        arena: &'a Arena<'a, A>,
        source: &'a dyn source::Source,
        formatter: crate::Formatter,
    ) -> Self {
        Printer {
            printer: pretty_types::Printer::new(arena, source),
            formatter,
        }
    }

    pub(super) fn format(&self, width: usize, hardline: &'a str, expr: &'a SpannedExpr<I>) -> String
    where
        A: Clone,
    {
        let doc = self.pretty_expr(expr).1;
        doc.pretty(width)
            .to_string()
            .lines()
            .map(|s| format!("{}{}", s.trim_end(), hardline))
            .collect()
    }

    fn pretty_expr(&self, expr: &'a SpannedExpr<I>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let e = self
            .pretty_expr_with_shebang_line(expr)
            .append(self.comments(Span::new(expr.span.end(), self.source.span().end())));
        e
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
                    _ => break,
                };
            }
        }

        let arena = self.arena;

        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start(), next);

        let span = Span::new(previous_end, expr.span.start());
        let comments = self.comments(span);
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
                            .intersperse(arena.text(",").append(arena.line())),
                    ),
                )
                .append("]")
                .group(),

            Expr::Block(ref elems) => {
                if elems.len() == 1 {
                    chain![arena, "(", pretty(&elems[0]), ")"]
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

            Expr::Ident(ref id) => pretty_types::ident(arena, id.name.as_ref() as &str),

            Expr::IfElse(..) => self.pretty_if_expr(expr),

            Expr::Infix {
                ref lhs,
                ref op,
                ref rhs,
                ..
            } => chain![
                arena,
                pretty(lhs).group(),
                chain![
                    arena,
                    hardline(arena, rhs),
                    op.value.name.as_ref() as &str,
                    " ",
                    pretty(rhs).group()
                ]
                .nest(INDENT)
            ]
            .group(),

            Expr::LetBindings(ref binds, ref body) => {
                let binding = |bind: &'a ValueBinding<I>| {
                    let decl = chain![
                        arena,
                        "let ",
                        chain![
                            arena,
                            self.pretty_pattern(&bind.name),
                            " ",
                            arena.concat(bind.args.iter().map(|arg| {
                                chain![
                                    arena,
                                    if arg.arg_type == ArgType::Implicit {
                                        arena.text("?")
                                    } else {
                                        arena.nil()
                                    },
                                    arena.text(arg.name.value.name.as_ref() as &str).append(" ")
                                ]
                            }))
                        ]
                        .group(),
                        match bind.typ {
                            None => arena.nil(),
                            Some(ref typ) => {
                                arena
                                    .text(": ")
                                    .append(types::pretty_print(self, typ))
                                    .append(self.space_after(typ.span().end()))
                                    .nest(INDENT)
                            }
                        },
                        "="
                    ]
                    .group();
                    chain![
                        arena,
                        pretty_types::doc_comment(arena, bind.metadata.comment()),
                        self.pretty_attributes(bind.metadata.attributes()),
                        self.hang(
                            decl,
                            (self.space_before(bind.expr.span.start()), true),
                            &bind.expr
                        )
                        .group(),
                        if self.formatter.expanded {
                            arena.hardline()
                        } else {
                            arena.nil()
                        }
                    ]
                };
                let is_recursive = match binds {
                    ValueBindings::Recursive(_) => true,
                    ValueBindings::Plain(_) => false,
                };
                chain![
                    arena,
                    if is_recursive {
                        arena.text("rec").append(if binds.len() == 1 {
                            arena.softline()
                        } else {
                            arena.hardline()
                        })
                    } else {
                        arena.nil()
                    },
                    arena.concat(
                        binds
                            .iter()
                            .map(|bind| binding(bind))
                            .interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))
                    ),
                    if is_recursive {
                        match body.value {
                            Expr::LetBindings(..) => arena.hardline().append(arena.text("in")),
                            _ => arena.nil(),
                        }
                    } else {
                        arena.nil()
                    },
                    self.pretty_expr_(binds.last().unwrap().span().end(), body)
                        .group()
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
                        Literal::String(ref s) => chain![arena, "\"", arena.text(&s[..]), "\""],
                        Literal::Char(c) => chain![arena, "'", arena.text(c.to_string()), "'"],
                    }
                }
            }

            Expr::Match(ref expr, ref alts) => chain![
                arena,
                chain![arena, "match ", pretty(expr), " with"].group(),
                arena.hardline(),
                arena.concat(
                    alts.iter()
                        .map(|alt| {
                            chain![
                                arena,
                                "| ",
                                self.pretty_pattern(&alt.pattern),
                                " ->",
                                self.hang(
                                    arena.nil(),
                                    (self.space_before(alt.expr.span.start()), true),
                                    &alt.expr
                                )
                                .group()
                            ]
                        })
                        .intersperse(arena.hardline())
                )
            ],

            Expr::Projection(ref expr, ref field, _) => chain![
                arena,
                pretty(expr),
                ".",
                pretty_types::ident(arena, field.as_ref() as &str)
            ],

            Expr::Record { .. } | Expr::Tuple { .. } | Expr::Lambda(_) => {
                self.hang(arena.nil(), (arena.nil(), false), expr)
            }

            Expr::TypeBindings(ref binds, ref body) => {
                let is_recursive = binds.len() > 1;

                chain![
                    arena,
                    if is_recursive && binds.len() != 1 {
                        arena.text("rec").append(arena.hardline())
                    } else {
                        arena.nil()
                    },
                    pretty_types::doc_comment(arena, binds.first().unwrap().metadata.comment()),
                    self.pretty_attributes(binds.first().unwrap().metadata.attributes()),
                    if is_recursive && binds.len() == 1 {
                        arena.text("rec").append(arena.line())
                    } else {
                        arena.nil()
                    },
                    arena.concat(
                        binds
                            .iter()
                            .enumerate()
                            .map(|(i, bind)| {
                                let typ = bind.alias.value.unresolved_type();
                                let typ = match **typ {
                                    // Remove the "parameters"
                                    Type::Forall(_, ref typ) => typ,
                                    _ => typ,
                                };
                                let mut type_doc = types::pretty_print(self, typ);
                                match **typ {
                                    Type::Record(_) | Type::Variant(_) => (),
                                    _ => type_doc = type_doc.nest(INDENT),
                                }
                                let variant = match &**typ {
                                    Type::Variant(row) => match &**row {
                                        Type::ExtendRow { fields, .. } => !fields.is_empty(),
                                        _ => false,
                                    },
                                    _ => false,
                                };
                                chain![
                                    arena,
                                    if i != 0 {
                                        chain![
                                            arena,
                                            pretty_types::doc_comment(
                                                arena,
                                                bind.metadata.comment()
                                            ),
                                            self.pretty_attributes(bind.metadata.attributes())
                                        ]
                                    } else {
                                        arena.nil()
                                    },
                                    "type",
                                    " ",
                                    bind.name.value.as_ref() as &str,
                                    " ",
                                    arena
                                        .concat(bind.alias.value.params().iter().map(|arg| {
                                            chain![
                                                arena,
                                                if *arg.kind != Kind::Type
                                                    && *arg.kind != Kind::Hole
                                                {
                                                    chain![
                                                        arena,
                                                        "(",
                                                        arg.id.as_ref() as &str,
                                                        " :",
                                                        arena.line(),
                                                        pretty_kind(arena, Prec::Top, &arg.kind)
                                                            .group(),
                                                        ")"
                                                    ]
                                                    .group()
                                                } else {
                                                    arena.text(arg.id.as_ref() as &str)
                                                },
                                                arena.line()
                                            ]
                                        }))
                                        .group(),
                                    "=",
                                    if variant {
                                        chain![arena, arena.hardline(), type_doc].nest(INDENT)
                                    } else {
                                        chain![arena, arena.space(), type_doc].group()
                                    }
                                ]
                                .group()
                            })
                            .interleave(newlines_iter!(self, binds.iter().map(|bind| bind.span())))
                    ),
                    if is_recursive {
                        arena.hardline().append(arena.text("in"))
                    } else {
                        arena.nil()
                    },
                    if self.formatter.expanded {
                        arena.hardline()
                    } else {
                        arena.nil()
                    },
                    self.pretty_expr_(binds.last().unwrap().alias.span.end(), body)
                ]
                .group()
            }

            Expr::Do(Do {
                ref id,
                ref bound,
                ref body,
                ..
            }) => {
                if self.source.src_slice(expr.span).starts_with("seq") {
                    let from = arena.text("seq");
                    chain![
                        arena,
                        self.hang(from, (self.space_before(bound.span.start()), true), bound),
                        self.pretty_expr_(bound.span.end(), body)
                    ]
                } else {
                    match id {
                        Some(pattern) => {
                            let from = chain![
                                arena,
                                "do",
                                self.space_before(pattern.span.start()),
                                self.pretty_pattern(pattern),
                                self.space_after(pattern.span.end()),
                                "="
                            ];
                            chain![
                                arena,
                                self.hang(
                                    from,
                                    (self.space_before(bound.span.start()), true),
                                    bound
                                ),
                                self.pretty_expr_(bound.span.end(), body)
                            ]
                        }

                        None => chain![
                            arena,
                            self.pretty_expr_(bound.span.start(), bound),
                            self.pretty_expr_(bound.span.end(), body)
                        ],
                    }
                }
            }
            Expr::MacroExpansion { ref original, .. } => {
                return self.pretty_expr_(previous_end, original);
            }
            Expr::Annotated(ref expr, ref typ) => chain![
                arena,
                pretty(expr).group(),
                arena.line(),
                ":",
                arena.line(),
                types::pretty_print(self, typ)
            ],
            Expr::Error(_) => arena.text("<error>"),
        };
        comments.append(doc)
    }

    fn space(&self, span: Span<BytePos>) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.whitespace(span, self.arena.line())
    }

    fn whitespace(
        &self,
        span: Span<BytePos>,
        default: DocBuilder<'a, Arena<'a, A>, A>,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        let (doc, _) = self.comments_count(span);
        if let Doc::Nil = *doc.1 {
            default
        } else {
            doc
        }
    }

    fn pretty_if_expr(&self, mut expr: &'a SpannedExpr<I>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start(), next);
        let arena = self.arena;

        let mut doc = arena.nil();
        let mut prefix: Option<DocBuilder<Arena<A>, A>> = None;
        while let Expr::IfElse(body, if_true, if_false) = &expr.value {
            let next = chain![
                arena,
                chain![
                    arena,
                    prefix
                        .map(|prefix| prefix.append(" "))
                        .unwrap_or_else(|| arena.nil()),
                    "if ",
                    pretty(body),
                    arena.line(),
                    "then"
                ]
                .group(),
                arena.line().append(pretty(if_true)).nest(INDENT).group(),
            ]
            .group();
            doc = doc.append(next).append(arena.line());
            prefix = Some(arena.text("else"));
            expr = if_false;
        }
        chain![
            arena,
            doc,
            chain![arena, prefix.unwrap(), arena.line(), pretty(expr),]
                .nest(INDENT)
                .group(),
        ]
    }

    fn pretty_lambda(
        &self,
        decls: &mut Vec<(
            (DocBuilder<'a, Arena<'a, A>, A>, bool),
            DocBuilder<'a, Arena<'a, A>, A>,
        )>,
        body_spacing: (DocBuilder<'a, Arena<'a, A>, A>, bool),
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
                let from = chain![
                    arena,
                    "\\",
                    arena.concat(lambda.args.iter().map(|arg| {
                        arena.text(arg.name.value.name.as_ref() as &str).append(" ")
                    })),
                    "->"
                ];
                decls.push((body_spacing, from));
                let (body, trailer) = self.pretty_lambda(
                    decls,
                    (self.space_before(lambda.body.span.start()), true),
                    &lambda.body,
                );
                (body, trailer)
            }
            Expr::Record {
                ref types,
                ref exprs,
                ref base,
                ..
            } => {
                decls.push((body_spacing, arena.text("{")));
                decls.push(((arena.nil(), false), arena.nil()));

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

                let mut line = hardline(arena, expr);
                // If there are any explicit line breaks then we need put each field on a separate
                // line
                let newline_in_fields = newlines
                    .iter()
                    .any(|&(ref l, ref r)| !is_nil(l) || !is_nil(r));
                let newline_from_doc_comment = expr.value.field_iter().any(|either| {
                    either
                        .either(|f| &f.metadata, |f| &f.metadata)
                        .comment()
                        .is_some()
                });
                let newline_in_base = base
                    .as_ref()
                    .map_or(false, |base| !is_nil(&self.space_before(base.span.start())));
                if newline_in_fields || newline_in_base | newline_from_doc_comment {
                    line = arena.hardline();
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
                                pretty_types::ident(arena, l.name.value.as_ref() as &str),
                            ),
                            Either::Right(r) => {
                                let id = pretty_types::ident(arena, r.name.value.as_ref() as &str);
                                let doc = chain![
                                    arena,
                                    pretty_types::doc_comment(arena, r.metadata.comment()),
                                    match r.value {
                                        Some(ref expr) => {
                                            let x = chain![
                                                arena,
                                                id,
                                                self.space_after(r.name.span.end()),
                                                "="
                                            ];
                                            self.hang(
                                                x,
                                                (self.space_before(expr.span.start()), true),
                                                expr,
                                            )
                                            .group()
                                        }
                                        None => id,
                                    }
                                ];
                                pos::spanned(r.name.span, doc)
                            }
                        }),
                        |spanned| spanned.value,
                    ))
                    .append(if !types.is_empty() || !exprs.is_empty() {
                        trailing_comma(arena)
                    } else {
                        arena.nil()
                    })
                    .append(match *base {
                        Some(ref base) => {
                            let comments = self.comments_after(last_field_end);
                            chain![
                                arena,
                                if let Doc::Nil = *comments.1 {
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
                    .group();

                (record, arena.text("}"))
            }

            Expr::Tuple {
                elems: [ref inner], ..
            } => {
                let decl = arena.text("(");

                decls.push((body_spacing, decl));

                let (body, end) = self.pretty_lambda(
                    decls,
                    (self.comments_before(inner.span.start()), true),
                    inner,
                );

                (body, end.append(")"))
            }

            Expr::Tuple { ref elems, .. } => {
                let pretty = |next: &'a SpannedExpr<_>| self.pretty_expr_(next.span.start(), next);

                decls.push((body_spacing, arena.text("(")));
                decls.push(((arena.nil(), true), arena.nil()));

                let inner = arena.concat(
                    self.comma_sep_paren(
                        elems
                            .iter()
                            .map(|elem| pos::spanned(elem.span, pretty(elem))),
                        |spanned| spanned.value,
                    ),
                );
                let tuple = chain![
                    arena,
                    self.nilline_after(expr.span.start() + ByteOffset::from(1)),
                    inner,
                    trailing_comma(arena),
                ]
                .group();

                let end = if elems.is_empty() {
                    arena.nil()
                } else {
                    self.nilline_before(expr.span.end() - ByteOffset::from(1))
                };
                (tuple, end.append(arena.text(")")))
            }

            _ => {
                let body_spacing = match &*(body_spacing.0).1 {
                    Doc::Nil if forced_new_line(expr) => (arena.hardline(), body_spacing.1),
                    Doc::FlatAlt(
                        pretty::RefDoc(Doc::Line),
                        pretty::RefDoc(Doc::BorrowedText(" ")),
                    ) if forced_new_line(expr) => (arena.hardline(), body_spacing.1),
                    _ => body_spacing,
                };
                decls.push((body_spacing, arena.nil()));
                (self.pretty_expr_(expr.span.start(), expr), arena.nil())
            }
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
            chain![
                arena,
                "#[",
                &attribute.name[..],
                match attribute.arguments {
                    Some(ref arguments) => chain![arena, "(", &arguments[..], ")"],
                    None => arena.nil(),
                },
                "]",
                arena.hardline()
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
                chain![
                    arena,
                    ident.value.as_ref() as &str,
                    " @ ",
                    self.pretty_pattern_(pat, Prec::Constructor)
                ],
            ),
            Pattern::Constructor(ref ctor, ref args) => {
                let doc = chain![
                    arena,
                    ctor.as_ref(),
                    arena.concat(args.iter().map(|arg| {
                        arena
                            .text(" ")
                            .append(self.pretty_pattern_(arg, Prec::Constructor))
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
                ref implicit_import,
                ..
            } => {
                let iter = self.comma_sep(
                    fields
                        .iter()
                        .map(|field| match field {
                            PatternField::Type { name } => {
                                pos::spanned(name.span, arena.text(name.value.as_ref() as &str))
                            }
                            PatternField::Value { name, value } => {
                                let doc = chain![
                                    arena,
                                    pretty_types::ident(arena, name.value.as_ref() as &str),
                                    match value {
                                        Some(ref new_name) => {
                                            chain![arena, " = ", self.pretty_pattern(new_name)]
                                        }
                                        None => arena.nil(),
                                    }
                                ];
                                pos::spanned(name.span, doc)
                            }
                        })
                        .chain(
                            implicit_import
                                .as_ref()
                                .map(|spanned| pos::spanned(spanned.span, arena.text("?"))),
                        ),
                    |spanned| spanned.value,
                );
                let doc = arena.concat(iter).nest(INDENT);
                chain![
                    arena,
                    "{",
                    doc,
                    if fields.is_empty() && implicit_import.is_none() {
                        arena.nil()
                    } else {
                        arena.line()
                    },
                    "}"
                ]
                .group()
            }
            Pattern::Tuple { ref elems, .. } => chain![
                arena,
                "(",
                arena.concat(
                    self.comma_sep_paren(
                        elems
                            .iter()
                            .map(|elem| pos::spanned(elem.span, self.pretty_pattern(elem))),
                        |elem| elem.value
                    )
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
        body_spacing: (DocBuilder<'a, Arena<'a, A>, A>, bool),
        expr: &'a SpannedExpr<I>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        let mut decls = Vec::new();
        decls.push(((self.arena.nil(), false), from));

        let (body, end) = self.pretty_lambda(&mut decls, body_spacing, expr);

        self.hang_parts(&decls, body, end).group()
    }

    fn hang_parts(
        &self,
        from: &[(
            (DocBuilder<'a, Arena<'a, A>, A>, bool),
            DocBuilder<'a, Arena<'a, A>, A>,
        )],
        body: DocBuilder<'a, Arena<'a, A>, A>,
        trailer: DocBuilder<'a, Arena<'a, A>, A>,
    ) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        A: Clone,
    {
        assert!(from.len() >= 1);
        let arena = self.arena;

        let mut iter = (1..from.len()).filter_map(|i| {
            let (before, after) = from.split_at(i);

            let before = before
                .iter()
                .rev()
                .cloned()
                .fold(arena.nil(), |next, ((body_spacing, _), from)| {
                    body_spacing.append(from).append(next).group()
                });

            let after = after.iter().rev().cloned().fold(
                body.clone(),
                |next, ((body_spacing, nest), from)| {
                    let doc = body_spacing.append(from).append(next);
                    if nest {
                        doc.nest(INDENT)
                    } else {
                        doc
                    }
                },
            );

            Some(
                if i != 1 {
                    arena.fail().flat_alt(arena.nil())
                } else {
                    // The last one should always apply
                    arena.nil()
                }
                .append(before)
                .group()
                .append(after)
                .append(trailer.clone())
                .group(),
            )
        });

        match iter.next() {
            None => unreachable!(),
            Some(first) => {
                let x = iter.fold(first, |a, b| b.union(a));

                x
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
                    arena.hardline()
                } else if comment.starts_with("//") {
                    arena.text(comment).append(arena.hardline())
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
    I: AsRef<str> + AsId<I> + std::fmt::Debug,
    F: FnMut(T) -> DocBuilder<'a, Arena<'a, A>, A>,
    J: Iterator<Item = T>,
    T: ::std::borrow::Borrow<Spanned<U, BytePos>>,
    A: std::fmt::Debug,
{
    type Item = DocBuilder<'a, Arena<'a, A>, A>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|item| {
            let span = item.borrow().span;
            let arena = self.printer.arena;
            let i = self.i;
            self.i += 1;
            chain![
                arena,
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
            let doc = chain![
                arena,
                pretty_kind(arena, Prec::Function, a),
                arena.line(),
                "-> ",
                pretty_kind(arena, Prec::Top, r)
            ];
            prec.enclose(Prec::Function, arena, doc)
        }
    }
}

fn hardline<'a, Id, A>(
    arena: &'a Arena<'a, A>,
    expr: &'a SpannedExpr<Id>,
) -> DocBuilder<'a, Arena<'a, A>, A> {
    if forced_new_line(expr) {
        arena.hardline()
    } else {
        arena.line()
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
