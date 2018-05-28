//! Source code locations (borrowed from rustc's [libsyntax_pos])
//!
//! [libsyntax_pos]: https://github.com/rust-lang/rust/blob/master/src/libsyntax_pos/lib.rs

use std::fmt;

pub use codespan::{
    ByteIndex as BytePos, ByteOffset, ColumnIndex as Column, ColumnOffset, LineIndex as Line,
    LineOffset, Span,
};

/// A location in a source file
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct Location {
    pub line: Line,
    pub column: Column,
    pub absolute: BytePos,
}

impl Location {
    pub fn shift(mut self, ch: char) -> Location {
        if ch == '\n' {
            self.line += LineOffset(1);
            self.column = Column(1);
        } else {
            self.column += ColumnOffset(1);
        }
        self.absolute += ByteOffset(ch.len_utf8() as i64);
        self
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Line: {}, Column: {}",
            self.line.number(),
            self.column.number()
        )
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Spanned<T, Pos> {
    pub span: Span<Pos>,
    pub value: T,
}

impl<T, Pos> Spanned<T, Pos> {
    pub fn map<U, F>(self, mut f: F) -> Spanned<U, Pos>
    where
        F: FnMut(T) -> U,
    {
        Spanned {
            span: self.span,
            value: f(self.value),
        }
    }
}

impl<T: fmt::Display, Pos: fmt::Display + Copy> fmt::Display for Spanned<T, Pos> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.span.start(), self.value)
    }
}

pub fn span<Pos>(start: Pos, end: Pos) -> Span<Pos>
where
    Pos: Ord,
{
    Span::new(start, end)
}

pub fn spanned<T, Pos>(span: Span<Pos>, value: T) -> Spanned<T, Pos>
where
    Pos: Ord,
{
    Spanned {
        span: span,
        value: value,
    }
}

pub fn spanned2<T, Pos>(start: Pos, end: Pos, value: T) -> Spanned<T, Pos>
where
    Pos: Ord,
{
    Spanned {
        span: span(start, end),
        value: value,
    }
}

pub trait HasSpan {
    fn span(&self) -> Span<BytePos>;
}
