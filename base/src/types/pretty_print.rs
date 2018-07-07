use std::borrow::Cow;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

use pretty::{Arena, Doc, DocAllocator, DocBuilder};

use ast::{is_operator_char, Commented};
use metadata::{Comment, CommentType};
use pos::{BytePos, HasSpan, Span};
use source::Source;

use types::{pretty_print, Type};

pub fn ident<'a, S, A>(arena: &'a Arena<'a, A>, name: S) -> DocBuilder<'a, Arena<'a, A>, A>
where
    S: Into<Cow<'a, str>>,
{
    let name = name.into();
    if name.starts_with(is_operator_char) {
        chain![arena; "(", name, ")"]
    } else {
        arena.text(name)
    }
}

pub fn doc_comment<'a, A>(
    arena: &'a Arena<'a, A>,
    text: Option<&'a Comment>,
) -> DocBuilder<'a, Arena<'a, A>, A> {
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

pub struct TypeFormatter<'a, I, T, A>
where
    I: 'a,
    T: 'a,
    A: 'a,
{
    width: usize,
    typ: &'a T,
    filter: &'a Fn(&I) -> Filter,
    annotate_symbol: &'a Fn(&I) -> Option<A>,
    _marker: PhantomData<I>,
}

impl<'a, I, T, A> TypeFormatter<'a, I, T, A> {
    pub fn new(typ: &'a T) -> Self {
        TypeFormatter {
            width: 80,
            typ: typ,
            filter: &|_| Filter::Retain,
            annotate_symbol: &|_| None,
            _marker: PhantomData,
        }
    }
}

impl<'a, I, T, A> TypeFormatter<'a, I, T, A> {
    pub fn width(mut self, width: usize) -> Self {
        self.width = width;
        self
    }

    pub fn filter(mut self, filter: &'a Fn(&I) -> Filter) -> Self {
        self.filter = filter;
        self
    }

    pub fn annotate_symbol(mut self, annotate_symbol: &'a Fn(&I) -> Option<A>) -> Self {
        self.annotate_symbol = annotate_symbol;
        self
    }

    pub fn pretty(&self, arena: &'a Arena<'a, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        T: Deref<Target = Type<I, T>> + HasSpan + Commented + 'a,
        I: AsRef<str>,
        A: Clone,
    {
        use super::top;
        top(self.typ).pretty(&Printer {
            arena,
            source: &(),
            filter: self.filter,
            annotate_symbol: self.annotate_symbol,
        })
    }

    pub fn build(&self, arena: &'a Arena<'a, A>, source: &'a Source) -> Printer<'a, I, A> {
        Printer {
            arena,
            source,
            filter: self.filter,
            annotate_symbol: self.annotate_symbol,
        }
    }
}

impl<'a, I, T> fmt::Display for TypeFormatter<'a, I, T, ()>
where
    T: Deref<Target = Type<I, T>> + HasSpan + Commented + 'a,
    I: AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = Arena::<()>::new();
        let source = &();
        let printer = self.build(&arena, source);
        let mut s = Vec::new();

        pretty_print(&printer, self.typ)
            .group()
            .1
            .render(self.width, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

pub struct Printer<'a, I: 'a, A: 'a> {
    pub arena: &'a Arena<'a, A>,
    pub source: &'a Source,
    filter: &'a Fn(&I) -> Filter,
    annotate_symbol: &'a Fn(&I) -> Option<A>,
}

impl<'a, I, A> Printer<'a, I, A> {
    pub fn new(arena: &'a Arena<'a, A>, source: &'a Source) -> Printer<'a, I, A> {
        Printer {
            arena,
            source,
            filter: &|_| Filter::Retain,
            annotate_symbol: &|_| None,
        }
    }

    pub fn filter(&self, field: &I) -> Filter {
        (self.filter)(field)
    }

    pub fn symbol(&self, symbol: &'a I) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        I: AsRef<str>,
    {
        let doc = self.arena.text(symbol.as_ref());
        match (self.annotate_symbol)(symbol) {
            Some(ann) => doc.annotate(ann),
            None => doc,
        }
    }

    pub fn space_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let (doc, comments) = self.comments_before_(pos);
        if let Doc::Nil = doc.1 {
            self.arena.space()
        } else if comments {
            self.arena.space().append(doc).append(self.arena.space())
        } else {
            doc
        }
    }

    pub fn space_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;
        let doc = self.comments_after(end);
        if let Doc::Nil = doc.1 {
            arena.space()
        } else {
            arena.space().append(doc)
        }
    }

    pub fn comments_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let (doc, comments) = self.comments_before_(pos);
        if comments {
            doc.append(self.arena.space())
        } else {
            doc
        }
    }

    fn comments_before_(&self, pos: BytePos) -> (DocBuilder<'a, Arena<'a, A>, A>, bool) {
        let arena = self.arena;

        if pos == 0.into() {
            return (arena.nil(), false);
        }

        let mut doc = arena.nil();
        let mut comments = 0;
        for comment in self
            .source
            .comments_between(Span::new(self.source.span().start(), pos))
            .rev()
        {
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

    pub fn comments_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let (doc, block_comments, _) =
            self.comments_count(Span::new(end, self.source.span().end()));
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

    pub fn comments_count(
        &self,
        span: Span<BytePos>,
    ) -> (DocBuilder<'a, Arena<'a, A>, A>, usize, bool) {
        let arena = self.arena;

        if span.start() == 0.into() {
            return (arena.nil(), 0, false);
        }

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
