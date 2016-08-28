//! Source code locations (borrowed from rustc's [libsyntax_pos])
//!
//! [libsyntax_pos]: https://github.com/rust-lang/rust/blob/ae774103501337ed63b42b673c6c4fdbf369e80e/src/libsyntax_pos/lib.rs

use std::cmp::{self, Ordering};
use std::fmt;
use std::ops::{Add, AddAssign, Sub, SubAssign};

/// A byte offset in a source string
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct BytePos(pub u32);

impl BytePos {
    pub fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

impl From<usize> for BytePos {
    fn from(src: usize) -> BytePos {
        BytePos(src as u32)
    }
}

impl Add for BytePos {
    type Output = BytePos;

    fn add(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() + rhs.to_usize()) as u32)
    }
}

impl AddAssign for BytePos {
    fn add_assign(&mut self, rhs: BytePos) {
        self.0 += rhs.0;
    }
}

impl Sub for BytePos {
    type Output = BytePos;

    fn sub(self, rhs: BytePos) -> BytePos {
        BytePos((self.to_usize() - rhs.to_usize()) as u32)
    }
}

impl SubAssign for BytePos {
    fn sub_assign(&mut self, rhs: BytePos) {
        self.0 -= rhs.0;
    }
}

impl fmt::Display for BytePos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A character position - usually used for column offsets
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CharPos(pub usize);

impl CharPos {
    pub fn to_usize(&self) -> usize {
        self.0
    }
}

impl From<usize> for CharPos {
    fn from(src: usize) -> CharPos {
        CharPos(src)
    }
}

impl Add for CharPos {
    type Output = CharPos;

    fn add(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() + rhs.to_usize())
    }
}

impl AddAssign for CharPos {
    fn add_assign(&mut self, rhs: CharPos) {
        self.0 += rhs.0;
    }
}

impl Sub for CharPos {
    type Output = CharPos;

    fn sub(self, rhs: CharPos) -> CharPos {
        CharPos(self.to_usize() - rhs.to_usize())
    }
}

impl SubAssign for CharPos {
    fn sub_assign(&mut self, rhs: CharPos) {
        self.0 -= rhs.0;
    }
}

impl fmt::Display for CharPos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// A location in a source file
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct Location {
    pub line: u32,
    pub column: CharPos,
    pub absolute: BytePos,
}

impl Location {
    pub fn bump(&mut self, ch: char) {
        if ch == '\n' {
            self.line += 1;
            self.column = CharPos(1);
        } else {
            self.column += CharPos(1);
        }
        self.absolute += BytePos::from(ch.len_utf8());
    }

    pub fn line_offset(mut self, offset: CharPos) -> Location {
        self.column += offset;
        self
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line: {}, Column: {}", self.line, self.column)
    }
}

/// A span between two locations in a source file
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct Span<Pos> {
    pub start: Pos,
    pub end: Pos,
}

impl<Pos: Ord> Span<Pos> {
    pub fn contains(self, other: Span<Pos>) -> bool {
        self.start <= other.start && other.end <= self.end
    }

    pub fn containment(self, pos: &Pos) -> Ordering {
        use std::cmp::Ordering::*;

        match (pos.cmp(&self.start), pos.cmp(&self.end)) {
            (Equal, _) | (_, Equal) | (Greater, Less) => Equal,
            (Less, _) => Less,
            (_, Greater) => Greater,
        }
    }

    pub fn containment_exclusive(self, pos: &Pos) -> Ordering {
        if self.end == *pos {
            Ordering::Greater
        } else {
            self.containment(pos)
        }
    }

    pub fn merge(self, other: Span<Pos>) -> Option<Span<Pos>> {
        if (self.start <= other.start && self.end > other.start) ||
           (self.start >= other.start && self.start < other.end) {
            Some(Span {
                start: cmp::min(self.start, other.start),
                end: cmp::max(self.end, other.end),
            })
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Spanned<T, Pos> {
    pub span: Span<Pos>,
    pub value: T,
}

impl<T: PartialEq, Pos> PartialEq for Spanned<T, Pos> {
    fn eq(&self, other: &Spanned<T, Pos>) -> bool {
        self.value == other.value
    }
}

impl<T: fmt::Display, Pos: fmt::Display> fmt::Display for Spanned<T, Pos> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.span.start, self.value)
    }
}

pub fn spanned<T, Pos>(span: Span<Pos>, value: T) -> Spanned<T, Pos> {
    Spanned {
        span: span,
        value: value,
    }
}

pub fn spanned2<T, Pos>(start: Pos, end: Pos, value: T) -> Spanned<T, Pos> {
    Spanned {
        span: Span {
            start: start,
            end: end,
        },
        value: value,
    }
}
