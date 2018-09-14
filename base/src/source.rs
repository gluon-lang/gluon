//! Module containing types and functions for mapping between byte indexes and line and column
//! locations

use pos::{BytePos, Line, Location, Span};

pub trait Source {
    fn new(s: &str) -> Self
    where
        Self: Sized;

    fn location(&self, byte: BytePos) -> Option<Location>;

    fn span(&self) -> Span<BytePos>;

    fn src(&self) -> &str;

    fn src_slice(&self, span: Span<BytePos>) -> &str;

    fn line_number_at_byte(&self, pos: BytePos) -> Option<Line>;

    /// Returns the starting position of any comments and whitespace before `end`
    fn comment_start_before(&self, end: BytePos) -> BytePos;

    fn comments_between(&self, span: Span<BytePos>) -> CommentIter;
}

impl Source for ::codespan::FileMap {
    fn new(s: &str) -> Self
    where
        Self: Sized,
    {
        ::codespan::FileMap::new("test".into(), s.into())
    }

    fn span(&self) -> Span<BytePos> {
        ::codespan::FileMap::span(self)
    }

    fn src(&self) -> &str {
        ::codespan::FileMap::src(self)
    }

    fn src_slice(&self, span: Span<BytePos>) -> &str {
        ::codespan::FileMap::src_slice(self, span).unwrap()
    }

    fn line_number_at_byte(&self, pos: BytePos) -> Option<Line> {
        self.find_line(pos).ok()
    }

    /// Returns the line and column location of `byte`
    fn location(&self, byte: BytePos) -> Option<Location> {
        ::codespan::FileMap::location(self, byte)
            .ok()
            .map(|(line, column)| Location {
                line,
                column,
                absolute: byte,
            })
    }

    /// Returns the starting position of any comments and whitespace before `end`
    fn comment_start_before(&self, end: BytePos) -> BytePos {
        let mut iter = self.comments_between(Span::new(BytePos::from(0), end));
        // Scan from `end` until a non comment token is found
        for _ in iter.by_ref().rev() {}
        BytePos::from(iter.src.len() as u32)
    }

    fn comments_between(&self, span: Span<BytePos>) -> CommentIter {
        CommentIter {
            src: self.src_slice(span).unwrap(),
        }
    }
}

impl Source for () {
    fn new(_: &str) -> Self
    where
        Self: Sized,
    {
    }

    fn span(&self) -> Span<BytePos> {
        Span::new(1.into(), 1.into())
    }

    fn src(&self) -> &str {
        ""
    }

    fn src_slice(&self, _: Span<BytePos>) -> &str {
        panic!("src_slice: Expected FileMap")
    }

    fn line_number_at_byte(&self, _: BytePos) -> Option<Line> {
        None
    }

    fn location(&self, _: BytePos) -> Option<Location> {
        None
    }

    fn comment_start_before(&self, pos: BytePos) -> BytePos {
        pos
    }

    fn comments_between(&self, _: Span<BytePos>) -> CommentIter {
        CommentIter { src: "" }
    }
}

pub struct CommentIter<'a> {
    src: &'a str,
}

impl<'a> Iterator for CommentIter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if self.src.is_empty() {
            None
        } else {
            self.src = self
                .src
                .trim_matches(|c: char| c.is_whitespace() && c != '\n');
            if self.src.starts_with("//") && !self.src.starts_with("///") {
                let comment_line = self.src.lines().next().unwrap();
                self.src = &self.src[comment_line.len()..];
                self.src = if self.src.starts_with("\r\n") {
                    &self.src[2..]
                } else {
                    // \n
                    &self.src[1..]
                };
                Some(comment_line)
            } else if self.src.starts_with("/*") {
                self.src.find("*/").map(|i| {
                    let (comment, rest) = self.src.split_at(i + 2);
                    self.src = rest;
                    comment
                })
            } else if self.src.starts_with('\n') {
                self.src = &self.src[1..];
                Some("")
            } else {
                None
            }
        }
    }
}

impl<'a> DoubleEndedIterator for CommentIter<'a> {
    fn next_back(&mut self) -> Option<&'a str> {
        if self.src.is_empty() {
            None
        } else {
            self.src = self
                .src
                .trim_right_matches(|c: char| c.is_whitespace() && c != '\n');
            if self.src.ends_with('\n') {
                let comment_line = self.src[..self.src.len() - 1].lines().next_back().unwrap();
                let trimmed = comment_line.trim_left();

                let newline_len = if self.src.ends_with("\r\n") { 2 } else { 1 };
                self.src = &self.src[..(self.src.len() - newline_len)];

                if trimmed.starts_with("//") && !trimmed.starts_with("///") {
                    self.src = &self.src[..(self.src.len() - 2 - trimmed.len() - 1)];
                    Some(trimmed)
                } else {
                    Some("")
                }
            } else if self.src.ends_with("*/") {
                self.src.rfind("/*").map(|i| {
                    let (rest, comment) = self.src.split_at(i);
                    self.src = rest;
                    comment
                })
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_comment_iter() {
        assert_eq!(CommentIter { src: "" }.next(), None);
    }
}
