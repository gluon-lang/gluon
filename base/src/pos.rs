//! Source code locations (borrowed from rustc's [libsyntax_pos])
//!
//! [libsyntax_pos]: https://github.com/rust-lang/rust/blob/master/src/libsyntax_pos/lib.rs

use std::{cmp, cmp::Ordering, fmt};

pub use codespan::{
    ByteIndex, ByteIndex as BytePos, ByteOffset, ColumnIndex as Column, ColumnOffset, Index,
    LineIndex as Line, LineOffset, RawIndex,
};

use crate::source::CodeMap;

/// A location in a source file
#[derive(Copy, Clone, Default, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct Location {
    pub line: Line,
    pub column: Column,
    pub absolute: BytePos,
}

impl Location {
    pub fn shift(&mut self, ch: u8) {
        if ch == b'\n' {
            self.line += LineOffset(1);
            self.column = Column(1);
        } else {
            self.column += ColumnOffset(1);
        }
        self.absolute += ByteOffset(1);
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

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Positioned<T, Pos> {
    pub pos: Pos,
    pub value: T,
}

/// A region of code in a source file
#[derive(Clone, Copy, Default, PartialEq, Eq, Ord, PartialOrd)]
#[cfg_attr(feature = "serialization", derive(Deserialize, Serialize))]
#[cfg_attr(feature = "memory_usage", derive(HeapSizeOf))]
pub struct Span<I> {
    start: I,
    end: I,
}

impl<I: fmt::Debug> fmt::Debug for Span<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}..{:?}", self.start, self.end)
    }
}

impl<I: Ord> Span<I> {
    /// Create a new span
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let span = Span::new(ByteIndex(3), ByteIndex(6));
    /// assert_eq!(span.start(), ByteIndex(3));
    /// assert_eq!(span.end(), ByteIndex(6));
    /// ```
    ///
    /// `start` and `end` are reordered to maintain the invariant that `start <= end`
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let span = Span::new(ByteIndex(6), ByteIndex(3));
    /// assert_eq!(span.start(), ByteIndex(3));
    /// assert_eq!(span.end(), ByteIndex(6));
    /// ```
    pub fn new(start: I, end: I) -> Span<I> {
        if start <= end {
            Span { start, end }
        } else {
            Span {
                start: end,
                end: start,
            }
        }
    }

    pub fn map<F, J>(self, mut f: F) -> Span<J>
    where
        F: FnMut(I) -> J,
        J: Ord,
    {
        Span::new(f(self.start), f(self.end))
    }
}

impl<I> Span<I> {
    /// Create a span like `new` but does not check that `start <= end`
    pub const fn new_unchecked(start: I, end: I) -> Span<I> {
        Span { start, end }
    }
}

impl<I> Span<I> {
    /// Get the start index
    pub fn start(self) -> I {
        self.start
    }

    /// Get the end index
    pub fn end(self) -> I {
        self.end
    }
}

impl<I: Index> Span<I> {
    /// Makes a span from offsets relative to the start of this span.
    pub fn subspan(&self, begin: I::Offset, end: I::Offset) -> Span<I> {
        assert!(end >= begin);
        assert!(self.start() + end <= self.end());
        Span {
            start: self.start() + begin,
            end: self.start() + end,
        }
    }

    /// Create a new span from a byte start and an offset
    pub fn from_offset(start: I, off: I::Offset) -> Span<I> {
        Span::new(start, start + off)
    }

    /// Return a new span with the low byte position replaced with the supplied byte position
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let span = Span::new(ByteIndex(3), ByteIndex(6));
    /// assert_eq!(span.with_start(ByteIndex(2)), Span::new(ByteIndex(2), ByteIndex(6)));
    /// assert_eq!(span.with_start(ByteIndex(5)), Span::new(ByteIndex(5), ByteIndex(6)));
    /// assert_eq!(span.with_start(ByteIndex(7)), Span::new(ByteIndex(6), ByteIndex(7)));
    /// ```
    pub fn with_start(self, start: I) -> Span<I> {
        Span::new(start, self.end())
    }

    /// Return a new span with the high byte position replaced with the supplied byte position
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let span = Span::new(ByteIndex(3), ByteIndex(6));
    /// assert_eq!(span.with_end(ByteIndex(7)), Span::new(ByteIndex(3), ByteIndex(7)));
    /// assert_eq!(span.with_end(ByteIndex(5)), Span::new(ByteIndex(3), ByteIndex(5)));
    /// assert_eq!(span.with_end(ByteIndex(2)), Span::new(ByteIndex(2), ByteIndex(3)));
    /// ```
    pub fn with_end(self, end: I) -> Span<I> {
        Span::new(self.start(), end)
    }

    /// Return true if `self` fully encloses `other`.
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let a = Span::new(ByteIndex(5), ByteIndex(8));
    ///
    /// assert_eq!(a.contains(a), true);
    /// assert_eq!(a.contains(Span::new(ByteIndex(6), ByteIndex(7))), true);
    /// assert_eq!(a.contains(Span::new(ByteIndex(6), ByteIndex(10))), false);
    /// assert_eq!(a.contains(Span::new(ByteIndex(3), ByteIndex(6))), false);
    /// ```
    pub fn contains(self, other: Span<I>) -> bool {
        self.start() <= other.start() && other.end() <= self.end()
    }

    pub fn contains_pos(self, other: I) -> bool {
        self.start() <= other && other <= self.end()
    }

    /// Return `Equal` if `self` contains `pos`, otherwise it returns `Less` if `pos` is before
    /// `start` or `Greater` if `pos` is after or at `end`.
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    /// use std::cmp::Ordering::*;
    ///
    /// let a = Span::new(ByteIndex(5), ByteIndex(8));
    ///
    /// assert_eq!(a.containment(ByteIndex(4)), Less);
    /// assert_eq!(a.containment(ByteIndex(5)), Equal);
    /// assert_eq!(a.containment(ByteIndex(6)), Equal);
    /// assert_eq!(a.containment(ByteIndex(8)), Equal);
    /// assert_eq!(a.containment(ByteIndex(9)), Greater);
    /// ```
    pub fn containment(self, pos: I) -> Ordering {
        use std::cmp::Ordering::*;

        match (pos.cmp(&self.start), pos.cmp(&self.end)) {
            (Equal, _) | (_, Equal) | (Greater, Less) => Equal,
            (Less, _) => Less,
            (_, Greater) => Greater,
        }
    }

    /// Return `Equal` if `self` contains `pos`, otherwise it returns `Less` if `pos` is before
    /// `start` or `Greater` if `pos` is *strictly* after `end`.
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    /// use std::cmp::Ordering::*;
    ///
    /// let a = Span::new(ByteIndex(5), ByteIndex(8));
    ///
    /// assert_eq!(a.containment_exclusive(ByteIndex(4)), Less);
    /// assert_eq!(a.containment_exclusive(ByteIndex(5)), Equal);
    /// assert_eq!(a.containment_exclusive(ByteIndex(6)), Equal);
    /// assert_eq!(a.containment_exclusive(ByteIndex(8)), Greater);
    /// assert_eq!(a.containment_exclusive(ByteIndex(9)), Greater);
    /// ```
    pub fn containment_exclusive(self, pos: I) -> Ordering {
        if self.end == pos {
            Ordering::Greater
        } else {
            self.containment(pos)
        }
    }

    /// Return a `Span` that would enclose both `self` and `end`.
    ///
    /// ```plain
    /// self     ~~~~~~~
    /// end                     ~~~~~~~~
    /// returns  ~~~~~~~~~~~~~~~~~~~~~~~
    /// ```
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let a = Span::new(ByteIndex(2), ByteIndex(5));
    /// let b = Span::new(ByteIndex(10), ByteIndex(14));
    ///
    /// assert_eq!(a.to(b), Span::new(ByteIndex(2), ByteIndex(14)));
    /// ```
    pub fn to(self, end: Span<I>) -> Span<I> {
        Span::new(
            cmp::min(self.start(), end.start()),
            cmp::max(self.end(), end.end()),
        )
    }

    /// Return a `Span` between the end of `self` to the beginning of `end`.
    ///
    /// ```plain
    /// self     ~~~~~~~
    /// end                     ~~~~~~~~
    /// returns         ~~~~~~~~~
    /// ```
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let a = Span::new(ByteIndex(2), ByteIndex(5));
    /// let b = Span::new(ByteIndex(10), ByteIndex(14));
    ///
    /// assert_eq!(a.between(b), Span::new(ByteIndex(5), ByteIndex(10)));
    /// ```
    pub fn between(self, end: Span<I>) -> Span<I> {
        Span::new(self.end(), end.start())
    }

    /// Return a `Span` between the beginning of `self` to the beginning of `end`.
    ///
    /// ```plain
    /// self     ~~~~~~~
    /// end                     ~~~~~~~~
    /// returns  ~~~~~~~~~~~~~~~~
    /// ```
    ///
    /// ```rust
    /// use gluon_base::pos::{ByteIndex, Span};
    ///
    /// let a = Span::new(ByteIndex(2), ByteIndex(5));
    /// let b = Span::new(ByteIndex(10), ByteIndex(14));
    ///
    /// assert_eq!(a.until(b), Span::new(ByteIndex(2), ByteIndex(10)));
    /// ```
    pub fn until(self, end: Span<I>) -> Span<I> {
        Span::new(self.start(), end.start())
    }
}

impl Span<BytePos> {
    pub fn to_range(self, source: &CodeMap) -> Option<std::ops::Range<usize>> {
        Some(source.to_usize(self.start())?..source.to_usize(self.end())?)
    }
}

impl<I: fmt::Display> fmt::Display for Span<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.start.fmt(f)?;
        write!(f, "..")?;
        self.end.fmt(f)?;
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Default)]
pub struct Spanned<T, Pos> {
    pub span: Span<Pos>,
    pub value: T,
}

impl<T, Pos> From<(T, Span<Pos>)> for Spanned<T, Pos> {
    fn from((value, span): (T, Span<Pos>)) -> Self {
        Spanned { span, value }
    }
}

impl<T, Pos> From<T> for Spanned<T, Pos>
where
    Pos: Default,
{
    fn from(value: T) -> Self {
        Spanned {
            span: Span::default(),
            value,
        }
    }
}

impl<T, Pos> PartialEq<T> for Spanned<T, Pos>
where
    T: PartialEq,
{
    fn eq(&self, other: &T) -> bool {
        self.value == *other
    }
}

impl<T, Pos> std::ops::Deref for Spanned<T, Pos> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T, Pos> std::ops::DerefMut for Spanned<T, Pos> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T, U, Pos> AsRef<U> for Spanned<T, Pos>
where
    T: AsRef<U>,
    U: ?Sized,
{
    fn as_ref(&self) -> &U {
        self.value.as_ref()
    }
}

impl<T, Pos> std::hash::Hash for Spanned<T, Pos>
where
    T: std::hash::Hash,
    Pos: std::hash::Hash + Copy,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.span.start().hash(state);
        self.span.end().hash(state);
        self.value.hash(state);
    }
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

pub fn spanned<T, Pos>(span: Span<Pos>, value: T) -> Spanned<T, Pos> {
    Spanned { span, value }
}

pub fn spanned2<T, Pos>(start: Pos, end: Pos, value: T) -> Spanned<T, Pos>
where
    Pos: Ord,
{
    spanned(span(start, end), value)
}

pub trait HasSpan {
    fn span(&self) -> Span<BytePos>;
}
