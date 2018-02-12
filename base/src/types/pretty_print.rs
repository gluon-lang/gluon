use std::borrow::Cow;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

use pretty::{Arena, DocAllocator, DocBuilder};

use ast::{is_operator_char, Comment, CommentType, Commented};
use pos::{BytePos, HasSpan, Span};
use source::Source;

use types::{pretty_print, Type};

pub fn ident<'b, S>(arena: &'b Arena<'b>, name: S) -> DocBuilder<'b, Arena<'b>>
where
    S: Into<Cow<'b, str>>,
{
    let name = name.into();
    if name.starts_with(is_operator_char) {
        chain![arena; "(", name, ")"]
    } else {
        arena.text(name)
    }
}

pub fn doc_comment<'a>(
    arena: &'a Arena<'a>,
    text: Option<&'a Comment>,
) -> DocBuilder<'a, Arena<'a>> {
    match text {
        Some(comment) => match comment.typ {
            CommentType::Line => arena.concat(
                comment
                    .content
                    .lines()
                    .map(|line| arena.text("/// ").append(line).append(arena.newline())),
            ),
            CommentType::Block => chain![arena;
                        "/**",
                        arena.newline(),
                        arena.concat(comment.content.lines().map(|line| {
                            let line = line.trim();
                            if line.is_empty() {
                                arena.newline()
                            } else {
                                chain![arena;
                                    " ",
                                    line,
                                    arena.newline()
                                ]
                            }
                        })),
                        "*/",
                        arena.newline()
                    ],
        },
        None => arena.nil(),
    }
}

#[derive(Debug, PartialEq)]
pub enum Filter {
    Drop,
    RetainKey,
    Retain,
}

impl From<bool> for Filter {
    fn from(b: bool) -> Filter {
        if b {
            Filter::Retain
        } else {
            Filter::Drop
        }
    }
}

pub struct TypeFormatter<'a, I, T>
where
    I: 'a,
    T: 'a,
{
    width: usize,
    typ: &'a T,
    filter: &'a Fn(&I) -> Filter,
    _marker: PhantomData<I>,
}

impl<'a, I, T> TypeFormatter<'a, I, T> {
    pub fn new(typ: &'a T) -> Self {
        TypeFormatter {
            width: 80,
            typ: typ,
            filter: &|_| Filter::Retain,
            _marker: PhantomData,
        }
    }
}

impl<'a, I, T> TypeFormatter<'a, I, T> {
    pub fn width(mut self, width: usize) -> Self {
        self.width = width;
        self
    }

    pub fn filter(mut self, filter: &'a Fn(&I) -> Filter) -> Self {
        self.filter = filter;
        self
    }

    pub fn pretty(&self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>>
    where
        T: Deref<Target = Type<I, T>> + HasSpan + Commented + 'a,
        I: AsRef<str>,
    {
        use super::top;
        top(self.typ).pretty(&Printer {
            arena,
            source: &Source::new(""),
            filter: self.filter,
        })
    }

    pub fn build<'e>(&self, arena: &'a Arena<'a>, source: &'e Source<'a>) -> Printer<'a, 'e, I> {
        Printer {
            arena,
            source,
            filter: self.filter,
        }
    }
}

impl<'a, I, T> fmt::Display for TypeFormatter<'a, I, T>
where
    T: Deref<Target = Type<I, T>> + HasSpan + Commented + 'a,
    I: AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = Arena::new();
        let source = Source::new("");
        let printer = self.build(&arena, &source);
        let mut s = Vec::new();

        pretty_print(&printer, self.typ)
            .group()
            .1
            .render(self.width, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

pub struct Printer<'a: 'e, 'e, I: 'a> {
    pub arena: &'a Arena<'a>,
    pub source: &'e Source<'a>,
    filter: &'a Fn(&I) -> Filter,
}

impl<'a: 'e, 'e, I> Printer<'a, 'e, I> {
    pub fn new(arena: &'a Arena<'a>, source: &'e Source<'a>) -> Printer<'a, 'e, I> {
        Printer {
            arena,
            source,
            filter: &|_| Filter::Retain,
        }
    }

    pub fn filter(&self, field: &I) -> Filter {
        (self.filter)(field)
    }

    pub fn space_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a>> {
        let (doc, comments) = self.comments_before_(pos);
        if doc.1 == self.arena.nil().1 {
            self.arena.space()
        } else if comments {
            self.arena.space().append(doc).append(self.arena.space())
        } else {
            doc
        }
    }

    pub fn space_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a>> {
        let arena = self.arena;
        let doc = self.comments_after(end);
        if doc.1 == arena.nil().1 {
            arena.space()
        } else {
            arena.space().append(doc)
        }
    }

    pub fn comments_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a>> {
        let (doc, comments) = self.comments_before_(pos);
        if comments {
            doc.append(self.arena.space())
        } else {
            doc
        }
    }

    fn comments_before_(&self, pos: BytePos) -> (DocBuilder<'a, Arena<'a>>, bool) {
        let arena = self.arena;
        let mut doc = arena.nil();
        let mut comments = 0;
        for comment in self.source.comments_between(Span::new(0.into(), pos)).rev() {
            let x = if comment.is_empty() {
                arena.newline()
            } else if comment.starts_with("//") {
                arena.text(comment).append(arena.newline())
            } else {
                comments += 1;
                arena.text(comment)
            };
            doc = x.append(doc);
        }
        (doc, comments != 0)
    }

    pub fn comments_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a>> {
        let (doc, block_comments, _) =
            self.comments_count(Span::new(end, self.source.src().len().into()));
        if block_comments == 0 {
            doc
        } else {
            let arena = self.arena;
            chain![arena;
                doc,
                arena.space()
            ]
        }
    }

    pub fn comments_count(&self, span: Span<BytePos>) -> (DocBuilder<'a, Arena<'a>>, usize, bool) {
        let arena = self.arena;
        let mut comments = 0;
        let mut ends_with_newline = false;
        let doc = arena.concat(self.source.comments_between(span).map(|comment| {
            ends_with_newline = false;
            if comment.is_empty() {
                ends_with_newline = true;
                arena.newline()
            } else if comment.starts_with("//") {
                arena.text(comment).append(arena.newline())
            } else {
                comments += 1;
                arena.text(comment)
            }
        }));
        (doc, comments, ends_with_newline)
    }
}
