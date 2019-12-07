use itertools::Itertools;
use pretty::{self, DocAllocator};

use crate::base::{
    symbol::Symbol,
    types::{Type, TypeExt},
};

use crate::core::{Alternative, Expr, Literal, Named, Pattern};

const INDENT: isize = 4;

fn ident<'a, A>(
    arena: &'a pretty::Arena<'a, A>,
    name: &'a Symbol,
) -> pretty::DocBuilder<'a, pretty::Arena<'a, A>, A> {
    // base::types::pretty_print::ident(arena, name.declared_name())
    base::types::pretty_print::ident(arena, format!("{:?}", name))
}

#[derive(Clone, Copy)]
pub enum Prec {
    Top,
    Arg,
}

impl Prec {
    pub fn enclose<'a>(
        &self,
        arena: &'a pretty::Arena<'a>,
        doc: pretty::DocBuilder<'a, pretty::Arena<'a>>,
    ) -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
        if let Prec::Arg = *self {
            chain![arena, "(", doc, ")"]
        } else {
            doc
        }
    }
}

fn pretty_literal<'a>(
    l: &Literal,
    arena: &'a pretty::Arena<'a>,
) -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
    match *l {
        Literal::Byte(b) => arena.text(format!("{}b", b)),
        Literal::Char(c) => arena.text(format!("{:?}", c)),
        Literal::Float(f) => arena.text(format!("{}", f)),
        Literal::Int(i) => arena.text(format!("{}", i)),
        Literal::String(ref s) => arena.text(format!("{:?}", s)),
    }
}

impl<'a> Expr<'a> {
    pub fn pretty(
        &'a self,
        arena: &'a pretty::Arena<'a>,
        prec: Prec,
    ) -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
        match *self {
            Expr::Call(f, args) => {
                let doc = chain![
                    arena,
                    f.pretty(arena, Prec::Arg),
                    arena
                        .concat(
                            args.iter()
                                .map(|arg| { arena.space().append(arg.pretty(arena, Prec::Arg)) })
                        )
                        .nest(INDENT)
                ]
                .group();
                prec.enclose(arena, doc).group()
            }
            Expr::Const(ref l, _) => pretty_literal(l, arena),
            Expr::Data(ref ctor, args, ..) => match &*ctor.typ {
                Type::Record(record) => chain![
                    arena,
                    "{",
                    chain![
                        arena,
                        arena.space(),
                        arena.concat(
                            record
                                .row_iter()
                                .zip(args)
                                .map(|(field, arg)| {
                                    chain![
                                        arena,
                                        field.name.as_str(),
                                        " =",
                                        chain![arena, arena.space(), arg.pretty(arena, Prec::Top)]
                                            .nest(INDENT),
                                        ","
                                    ]
                                    .group()
                                })
                                .intersperse(arena.space())
                        )
                    ]
                    .nest(INDENT),
                    arena.space(),
                    "}"
                ]
                .group(),
                typ if typ.is_array() => chain![
                    arena,
                    "[",
                    arena
                        .concat(args.iter().map(|arg| {
                            chain![arena, arena.space(), arg.pretty(arena, Prec::Top), ","].group()
                        }))
                        .nest(INDENT),
                    "]"
                ]
                .group(),
                _ => {
                    let doc = chain![
                        arena,
                        ctor.as_ref(),
                        arena.concat(
                            args.iter()
                                .map(|arg| { arena.space().append(arg.pretty(arena, Prec::Arg)) })
                        )
                    ]
                    .group();
                    prec.enclose(arena, doc)
                }
            },
            Expr::Ident(ref id, _) => chain![
                arena,
                if id.name.is_global() { "@" } else { "" },
                ident(arena, &id.name)
            ],
            Expr::Let(ref bind, ref expr) => {
                let doc = chain![
                    arena,
                    match bind.expr {
                        Named::Expr(ref expr) => {
                            chain![
                                arena,
                                chain![
                                    arena,
                                    "let ",
                                    ident(arena, &bind.name.name),
                                    arena.space(),
                                    "="
                                ]
                                .group(),
                                chain![
                                    arena,
                                    arena.space(),
                                    expr.pretty(arena, Prec::Top),
                                    arena.space()
                                ]
                                .group()
                                .nest(INDENT),
                                arena.hardline()
                            ]
                            .group()
                        }
                        Named::Recursive(ref closures) => {
                            arena.concat(closures.iter().map(|closure| {
                                chain![
                                    arena,
                                    chain![
                                        arena,
                                        "rec let ",
                                        ident(arena, &closure.name.name),
                                        chain![
                                            arena,
                                            arena.concat(closure.args.iter().map(|arg| {
                                                arena.space().append(arena.text(arg.as_ref()))
                                            })),
                                            arena.space(),
                                            "="
                                        ]
                                        .nest(INDENT)
                                    ]
                                    .group(),
                                    chain![
                                        arena,
                                        arena.space(),
                                        closure.expr.pretty(arena, Prec::Top),
                                        arena.space()
                                    ]
                                    .group()
                                    .nest(INDENT),
                                    arena.hardline()
                                ]
                                .group()
                            }))
                        }
                    },
                    "in",
                    arena.hardline(),
                    expr.pretty(arena, Prec::Top)
                ];
                prec.enclose(arena, doc)
            }
            Expr::Match(expr, alts) => match alts.first() {
                Some(
                    alt
                    @
                    &Alternative {
                        pattern: Pattern::Record { .. },
                        ..
                    },
                ) if alts.len() == 1 => match (&alt.pattern, &alt.expr) {
                    (Pattern::Record { fields: binds, .. }, Expr::Ident(id, ..))
                        if binds.len() == 1 && *id == binds[0].0 =>
                    {
                        chain![
                            arena,
                            expr.pretty(arena, Prec::Arg),
                            ".",
                            binds[0].0.name.declared_name()
                        ]
                    }
                    (Pattern::Record { .. }, _) => {
                        let doc = chain![arena,
                            "let ",
                            chain![arena,
                                alt.pattern.pretty(arena),
                                arena.space(),
                                "="
                            ].group(),
                            expr.pretty(arena, Prec::Top).nest(INDENT),
                            arena.hardline(),
                            "in",
                            arena.hardline(),
                            alt.expr.pretty(arena, Prec::Top).group(),
                            arena.hardline(),
                        ]
                        .group();
                        prec.enclose(arena, doc)
                    }

                    _ => {
                        let doc = chain![
                            arena,
                            "match ",
                            expr.pretty(arena, Prec::Top).nest(INDENT),
                            " with",
                            arena.hardline(),
                            chain![arena, "| ", alt.pattern.pretty(arena), arena.space(), "->"]
                                .group(),
                            arena.hardline(),
                            alt.expr.pretty(arena, Prec::Top).nest(INDENT).group(),
                            arena.hardline(),
                            "end"
                        ]
                        .group();
                        prec.enclose(arena, doc)
                    }
                },
                _ => {
                    let doc = chain![
                        arena,
                        "match ",
                        expr.pretty(arena, Prec::Top).nest(INDENT),
                        " with",
                        arena.hardline(),
                        arena.concat(
                            alts.iter()
                                .map(|alt| {
                                    chain![
                                        arena,
                                        "| ",
                                        alt.pattern.pretty(arena),
                                        " ->",
                                        arena.space(),
                                        alt.expr.pretty(arena, Prec::Top).nest(INDENT).group()
                                    ]
                                    .nest(INDENT)
                                })
                                .intersperse(arena.hardline())
                        ),
                        arena.hardline(),
                        "end"
                    ]
                    .group();
                    prec.enclose(arena, doc)
                }
            },

            Expr::Cast(expr, ref typ) => chain![
                arena,
                expr.pretty(arena, prec),
                arena.space(),
                ": ",
                typ.pretty(arena)
            ]
            .group(),
        }
    }
}

impl Pattern {
    pub fn pretty<'a>(
        &'a self,
        arena: &'a pretty::Arena<'a>,
    ) -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
        match *self {
            Pattern::Constructor(ref ctor, ref args) => chain![
                arena,
                ctor.as_ref(),
                arena.concat(
                    args.iter()
                        .map(|arg| { arena.space().append(ident(arena, &arg.name)) })
                )
            ]
            .group(),
            Pattern::Ident(ref id) => arena.text(id.as_ref()),
            Pattern::Record { ref fields, .. } => chain![
                arena,
                "{",
                arena
                    .concat(
                        fields
                            .iter()
                            .map(|&(ref field, ref value)| {
                                chain![
                                    arena,
                                    arena.space(),
                                    ident(arena, &field.name),
                                    match *value {
                                        Some(ref value) => {
                                            chain![arena, "=", arena.space(), ident(arena, value)]
                                        }
                                        None => arena.nil(),
                                    }
                                ]
                            })
                            .intersperse(arena.text(","))
                    )
                    .nest(INDENT),
                arena.space(),
                "}"
            ]
            .group(),
            Pattern::Literal(ref l) => pretty_literal(l, arena),
        }
    }
}
