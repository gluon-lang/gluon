//! Source code locations (borrowed from rustc's [libsyntax_pos])
//!
//! [libsyntax_pos]: https://github.com/rust-lang/rust/blob/master/src/libsyntax_pos/lib.rs

use std::cmp::{self, Ordering};
use std::fmt;
use std::ops::{Add, AddAssign, Sub, SubAssign};

macro_rules! pos_struct {
    (#[$doc:meta] pub struct $Pos:ident($T:ty);) => {
        #[$doc]
        #[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[cfg_attr(feature = "serde_derive", derive(Serialize, Deserialize))]
        pub struct $Pos($T);

        impl fmt::Debug for $Pos {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl $Pos {
            pub fn to_usize(&self) -> usize {
                self.0 as usize
            }
        }

        impl From<usize> for $Pos {
            fn from(src: usize) -> $Pos {
                $Pos(src as $T)
            }
        }

        impl Add for $Pos {
            type Output = $Pos;

            fn add(self, rhs: $Pos) -> $Pos {
                $Pos::from(self.to_usize() + rhs.to_usize())
            }
        }

        impl AddAssign for $Pos {
            fn add_assign(&mut self, rhs: $Pos) {
                self.0 += rhs.0;
            }
        }

        impl Sub for $Pos {
            type Output = $Pos;

            fn sub(self, rhs: $Pos) -> $Pos {
                $Pos::from(self.to_usize() - rhs.to_usize())
            }
        }

        impl SubAssign for $Pos {
            fn sub_assign(&mut self, rhs: $Pos) {
                self.0 -= rhs.0;
            }
        }
    };
}

pos_struct! {
    /// A byte offset in a source string
    pub struct BytePos(u32);
}

impl fmt::Display for BytePos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

pos_struct! {
    /// A `0`-indexed column number, displayed externally as if it were offset from `1`.
    pub struct Column(u32);
}

impl fmt::Display for Column {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self.0 + 1).fmt(f)
    }
}

pos_struct! {
    /// A `0`-indexed line number, displayed externally as if it were offset from `1`.
    pub struct Line(u32);
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self.0 + 1).fmt(f)
    }
}

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
            self.line += Line::from(1);
            self.column = Column::from(1);
        } else {
            self.column += Column::from(1);
        }
        self.absolute += BytePos::from(ch.len_utf8());
        self
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line: {}, Column: {}", self.line, self.column)
    }
}

/// An expansion identifier tracks whether a span originated from a macro expansion or not.
#[derive(Copy, Clone, Default, Ord, PartialOrd, Eq, PartialEq, Debug)]
pub struct ExpansionId(pub u32);

pub const NO_EXPANSION: ExpansionId = ExpansionId(0);

pub const UNKNOWN_EXPANSION: ExpansionId = ExpansionId(1);

/// A span between two locations in a source file
#[derive(Copy, Clone, Default, Eq, Debug)]
pub struct Span<Pos> {
    pub start: Pos,
    pub end: Pos,
    pub expansion_id: ExpansionId,
}

impl<Pos> PartialEq for Span<Pos>
where
    Pos: PartialEq,
{
    fn eq(&self, other: &Span<Pos>) -> bool {
        self.start == other.start && self.end == other.end
    }
}

impl<Pos> PartialOrd for Span<Pos>
where
    Pos: PartialOrd,
{
    fn partial_cmp(&self, other: &Span<Pos>) -> Option<Ordering> {
        self.start.partial_cmp(&other.start).and_then(|ord| {
            if ord == Ordering::Equal {
                self.end.partial_cmp(&self.end)
            } else {
                Some(ord)
            }
        })
    }
}

impl<Pos> Ord for Span<Pos>
where
    Pos: Ord,
{
    fn cmp(&self, other: &Span<Pos>) -> Ordering {
        let ord = self.start.cmp(&other.start);
        if ord == Ordering::Equal {
            self.end.cmp(&self.end)
        } else {
            ord
        }
    }
}

impl<Pos: Ord> Span<Pos> {
    pub fn new(start: Pos, end: Pos) -> Span<Pos> {
        Span::with_id(start, end, NO_EXPANSION)
    }

    pub fn with_id(start: Pos, end: Pos, no_expansion: ExpansionId) -> Span<Pos> {
        // FIXME #416
        // debug_assert!(start <= end, "Invalid span");
        Span {
            start: start,
            end: end,
            expansion_id: no_expansion,
        }
    }

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
        assert!(self.expansion_id == other.expansion_id);
        if (self.start <= other.start && self.end > other.start)
            || (self.start >= other.start && self.start < other.end)
        {
            Some(Span {
                start: cmp::min(self.start, other.start),
                end: cmp::max(self.end, other.end),
                expansion_id: self.expansion_id,
            })
        } else {
            None
        }
    }

    pub fn map<Pos2, F>(self, mut f: F) -> Span<Pos2>
    where
        F: FnMut(Pos) -> Pos2,
    {
        Span {
            start: f(self.start),
            end: f(self.end),
            expansion_id: self.expansion_id,
        }
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

impl<T: fmt::Display, Pos: fmt::Display> fmt::Display for Spanned<T, Pos> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.span.start, self.value)
    }
}

pub fn span<Pos>(start: Pos, end: Pos) -> Span<Pos> {
    Span {
        start: start,
        end: end,
        expansion_id: NO_EXPANSION,
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
        span: span(start, end),
        value: value,
    }
}

pub trait HasSpan {
    fn span(&self) -> Span<BytePos>;
}
