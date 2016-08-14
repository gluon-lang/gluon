//! Source code locations (borrowed from rustc's [libsyntax_pos])
//!
//! [libsyntax_pos]: https://github.com/rust-lang/rust/blob/ae774103501337ed63b42b673c6c4fdbf369e80e/src/libsyntax_pos/lib.rs

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
