use std::{borrow::Cow, fmt, marker::PhantomData};

use pretty::{Arena, Doc, DocAllocator, DocBuilder};

use crate::{
    ast::{is_operator_char, HasMetadata},
    metadata::{Comment, CommentType},
    pos::{BytePos, HasSpan, Span},
    source::Source,
    types::AsId,
};

use crate::types::{pretty_print, TypePtr};

pub fn ident<'a, S, A>(arena: &'a Arena<'a, A>, name: S) -> DocBuilder<'a, Arena<'a, A>, A>
where
    S: Into<Cow<'a, str>>,
{
    let name = name.into();
    if name.starts_with(is_operator_char) {
        chain![arena, "(", name, ")"]
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
                    .map(|line| arena.text("/// ").append(line).append(arena.hardline())),
            ),
            CommentType::Block => chain![
                arena,
                "/**",
                arena.hardline(),
                arena.concat(comment.content.lines().map(|line| {
                    let line = line.trim();
                    if line.is_empty() {
                        arena.hardline()
                    } else {
                        chain![arena, " ", line, arena.hardline()]
                    }
                })),
                "*/",
                arena.hardline()
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
    filter: &'a dyn Fn(&I) -> Filter,
    symbol_text: &'a dyn Fn(&I) -> &str,
    annotate_symbol: &'a dyn Fn(&I) -> Option<A>,
    _marker: PhantomData<I>,
}

impl<'a, I, T, A> TypeFormatter<'a, I, T, A>
where
    I: AsRef<str>,
{
    pub fn new(typ: &'a T) -> Self {
        TypeFormatter {
            width: 80,
            typ,
            filter: &|_| Filter::Retain,
            annotate_symbol: &|_| None,
            symbol_text: &|s: &I| s.as_ref(),
            _marker: PhantomData,
        }
    }
}

impl<'a, I, T, A> TypeFormatter<'a, I, T, A> {
    pub fn width(mut self, width: usize) -> Self {
        self.width = width;
        self
    }

    pub fn filter(mut self, filter: &'a dyn Fn(&I) -> Filter) -> Self {
        self.filter = filter;
        self
    }

    pub fn annotate_symbol(mut self, annotate_symbol: &'a dyn Fn(&I) -> Option<A>) -> Self {
        self.annotate_symbol = annotate_symbol;
        self
    }

    pub fn symbol_text(mut self, symbol_text: &'a dyn Fn(&I) -> &str) -> Self {
        self.symbol_text = symbol_text;
        self
    }

    pub fn pretty(&self, arena: &'a Arena<'a, A>) -> DocBuilder<'a, Arena<'a, A>, A>
    where
        T: TypePtr<Id = I> + HasSpan + HasMetadata + 'a,
        I: AsRef<str>,
        T::SpannedId: AsRef<str> + AsId<I>,
        A: Clone,
    {
        use super::top;
        top(self.typ).pretty(&Printer {
            arena,
            source: &(),
            filter: self.filter,
            symbol_text: self.symbol_text,
            annotate_symbol: self.annotate_symbol,
        })
    }

    pub fn build(&self, arena: &'a Arena<'a, A>, source: &'a dyn Source) -> Printer<'a, I, A> {
        Printer {
            arena,
            source,
            filter: self.filter,
            symbol_text: self.symbol_text,
            annotate_symbol: self.annotate_symbol,
        }
    }
}

impl<'a, I, T> fmt::Display for TypeFormatter<'a, I, T, ()>
where
    T: TypePtr<Id = I> + HasSpan + HasMetadata + 'a,
    T::SpannedId: AsRef<str> + AsId<I>,
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
    pub source: &'a dyn Source,
    filter: &'a dyn Fn(&I) -> Filter,
    symbol_text: &'a dyn Fn(&I) -> &str,
    annotate_symbol: &'a dyn Fn(&I) -> Option<A>,
}

impl<'a, I, A> Printer<'a, I, A> {
    pub fn new(arena: &'a Arena<'a, A>, source: &'a dyn Source) -> Self
    where
        I: AsRef<str>,
    {
        Printer {
            arena,
            source,
            filter: &|_| Filter::Retain,
            symbol_text: &|s: &I| s.as_ref(),
            annotate_symbol: &|_| None,
        }
    }

    pub fn filter(&self, field: &I) -> Filter {
        (self.filter)(field)
    }

    pub fn symbol(&self, symbol: &'a I) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.symbol_with(symbol, (self.symbol_text)(symbol))
    }

    pub fn symbol_with(&self, symbol: &'a I, text: &'a str) -> DocBuilder<'a, Arena<'a, A>, A> {
        let doc = self.arena.text(text);
        match (self.annotate_symbol)(symbol) {
            Some(ann) => doc.annotate(ann),
            None => doc,
        }
    }

    pub fn space_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let doc = self.comments_before(pos);
        if let Doc::Nil = *doc.1 {
            self.arena.line()
        } else {
            doc
        }
    }

    pub fn space_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;
        let doc = self.comments_after(end);
        if let Doc::Nil = *doc.1 {
            arena.line()
        } else {
            doc
        }
    }

    pub fn nilline_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let doc = self.comments_before(pos);
        if let Doc::Nil = *doc.1 {
            self.arena.line_()
        } else {
            doc
        }
    }

    pub fn nilline_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let arena = self.arena;
        let doc = self.comments_after(end);
        if let Doc::Nil = *doc.1 {
            arena.line_()
        } else {
            doc
        }
    }

    pub fn comments_before(&self, pos: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        if pos == BytePos::default() {
            return self.arena.nil();
        }
        let (comments_after, mut doc, comments_before) = self.make_comments_doc(
            pos,
            self.source
                .comments_between(Span::new(self.source.span().start(), pos))
                .rev(),
            |l, r| r.append(l),
        );
        doc = match comments_before {
            CommentLike::Line | CommentLike::Block => self.arena.line().append(doc),
            CommentLike::Empty => doc,
        };
        doc = match comments_after {
            CommentLike::Block => doc.append(self.arena.line()),
            CommentLike::Line | CommentLike::Empty => doc,
        };
        doc
    }

    pub fn comments_after(&self, end: BytePos) -> DocBuilder<'a, Arena<'a, A>, A> {
        let (doc, _) = self.comments_count(Span::new(end, self.source.span().end()));
        doc
    }

    pub fn comments_count(&self, span: Span<BytePos>) -> (DocBuilder<'a, Arena<'a, A>, A>, usize) {
        if span.start() == BytePos::default() || span.end() == BytePos::default() {
            return (self.arena.nil(), 0);
        }

        let mut comments = 0;
        let (comments_before, mut doc, comments_after) = self.make_comments_doc(
            span.start(),
            self.source.comments_between(span).inspect(|comment| {
                if !comment.is_empty() {
                    comments += 1
                }
            }),
            |l, r| l.append(r),
        );

        match comments_before {
            CommentLike::Line | CommentLike::Block => {
                // Avoid inserting an extra space before comments at the start of the file
                if self.source.span().start() != span.start() {
                    doc = self.arena.line().append(doc)
                }
            }
            CommentLike::Empty => (),
        }
        doc = match comments_after {
            CommentLike::Block => doc.append(self.arena.line()),
            CommentLike::Line | CommentLike::Empty => doc,
        };
        (doc, comments)
    }

    fn make_comments_doc(
        &self,
        pos: BytePos,
        iterable: impl IntoIterator<Item = &'a str>,
        mut append: impl FnMut(
            DocBuilder<'a, Arena<'a, A>, A>,
            DocBuilder<'a, Arena<'a, A>, A>,
        ) -> DocBuilder<'a, Arena<'a, A>, A>,
    ) -> (CommentLike, DocBuilder<'a, Arena<'a, A>, A>, CommentLike) {
        let arena = self.arena;

        if pos == 0.into() {
            return (CommentLike::Empty, arena.nil(), CommentLike::Empty);
        }

        let mut doc = arena.nil();
        let mut comments_before = CommentLike::Empty;
        let mut comments_after = CommentLike::Empty;
        for (i, comment) in iterable.into_iter().enumerate() {
            let x = if comment.is_empty() {
                comments_after = CommentLike::Empty;
                arena.hardline()
            } else if comment.starts_with("//") {
                if i == 0 {
                    comments_before = CommentLike::Line;
                }
                comments_after = CommentLike::Line;

                arena.text(comment).append(arena.hardline())
            } else {
                if i == 0 {
                    comments_before = CommentLike::Block;
                }
                comments_after = CommentLike::Block;

                arena.text(comment)
            };
            doc = append(doc, x);
        }

        (comments_before, doc, comments_after)
    }
}

#[derive(Debug)]
enum CommentLike {
    Block,
    Line,
    Empty,
}
