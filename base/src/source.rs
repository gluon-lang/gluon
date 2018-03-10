//! Module containing types and functions for mapping between byte indexes and line and column
//! locations

use pos::{BytePos, Column, Line, Location, Span};

/// Type which provides a bidirectional mapping between byte offsets and line and column locations
/// for some source file
#[derive(Clone, Debug)]
pub struct Lines {
    starting_bytes: Vec<BytePos>,
    end: usize,
}

impl Lines {
    /// Creates a mapping for `src`
    pub fn new<I>(src: I) -> Lines
    where
        I: IntoIterator<Item = u8>,
    {
        use std::iter;

        let mut len = 0;
        let starting_bytes = {
            let input_indices = src.into_iter()
                .inspect(|_| len += 1)
                .enumerate()
                .filter(|&(_, b)| b == b'\n')
                .map(|(i, _)| BytePos::from(i + 1)); // index of first char in the line

            iter::once(BytePos::from(0)).chain(input_indices).collect()
        };
        Lines {
            starting_bytes,
            end: len,
        }
    }

    /// Returns the byte offset of the start of `line_number`
    pub fn line(&self, line_number: Line) -> Option<BytePos> {
        let line_number = line_number.to_usize();
        self.starting_bytes.get(line_number).cloned()
    }

    pub fn offset(&self, line: Line, column: Column) -> Option<BytePos> {
        self.line(line).and_then(|mut offset| {
            offset += BytePos::from(column.to_usize());
            if offset.to_usize() >= self.end {
                None
            } else {
                Some(offset)
            }
        })
    }

    /// Returns the line and column location of `byte`
    pub fn location(&self, byte: BytePos) -> Option<Location> {
        if byte.to_usize() <= self.end {
            let line_index = self.line_number_at_byte(byte);

            self.line(line_index).map(|line_byte| Location {
                line: line_index,
                column: Column::from((byte - line_byte).to_usize()),
                absolute: byte,
            })
        } else {
            None
        }
    }

    /// Returns which line `byte` points to
    pub fn line_number_at_byte(&self, byte: BytePos) -> Line {
        let num_lines = self.starting_bytes.len();

        Line::from(
            (0..num_lines)
                .filter(|&i| self.starting_bytes[i] > byte)
                .map(|i| i - 1)
                .next()
                .unwrap_or(num_lines - 1),
        )
    }
}

/// Type which provides a bidirectional mapping between byte offsets and line and column locations
#[derive(Clone, Debug)]
pub struct Source<'a> {
    src: &'a str,
    /// The starting byte position of each line in `src`
    lines: Lines,
}

impl<'a> Source<'a> {
    pub fn new(src: &str) -> Source {
        Source::with_lines(src, Lines::new(src.as_bytes().iter().cloned()))
    }

    pub fn with_lines(src: &str, lines: Lines) -> Source {
        Source { src, lines }
    }

    /// Returns the string which defines the source
    pub fn src(&self) -> &'a str {
        self.src
    }

    pub fn lines(&self) -> &Lines {
        &self.lines
    }

    /// Returns the byte offset and source of `line_number`
    pub fn line(&self, line_number: Line) -> Option<(BytePos, &str)> {
        self.lines.line(line_number).map(|start| {
            let line = match self.lines.starting_bytes.get(line_number.to_usize() + 1) {
                Some(end) => &self.src[start.to_usize()..end.to_usize() - 1], // Skip '\n'
                None => &self.src[start.to_usize()..],
            };

            (start, line)
        })
    }

    /// Returns the line number and the source at `byte`
    pub fn line_at_byte(&self, byte: BytePos) -> Option<(BytePos, &str)> {
        let line_number = self.line_number_at_byte(byte);
        self.line(line_number)
    }

    /// Returns which line `byte` points to
    pub fn line_number_at_byte(&self, byte: BytePos) -> Line {
        self.lines.line_number_at_byte(byte)
    }

    /// Returns the line and column location of `byte`
    pub fn location(&self, byte: BytePos) -> Option<Location> {
        self.lines.location(byte)
    }

    /// Returns the starting position of any comments and whitespace before `end`
    pub fn comment_start_before(&self, end: BytePos) -> BytePos {
        let mut iter = self.comments_between(Span::new(BytePos::from(0), end));
        // Scan from `end` until a non comment token is found
        for _ in iter.by_ref().rev() {}
        BytePos::from(iter.src.len())
    }

    pub fn comments_between(&self, span: Span<BytePos>) -> CommentIter<'a> {
        CommentIter {
            src: &self.src[span.start.to_usize()..span.end.to_usize()],
        }
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
            self.src = self.src
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
            } else if self.src.starts_with("\n") {
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
            self.src = self.src
                .trim_right_matches(|c: char| c.is_whitespace() && c != '\n');
            if self.src.ends_with("\n") {
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
    use pos::{BytePos, Column, Line, Location};

    use super::Source;

    fn test_source() -> Source<'static> {
        Source::new("hello!\nhowdy\n\nhi萤\nbloop\n")
    }

    #[test]
    fn source_line() {
        let source = test_source();

        assert_eq!(
            source.line(Line::from(0)),
            Some((BytePos::from(0), "hello!"))
        );
        assert_eq!(
            source.line(Line::from(1)),
            Some((BytePos::from(7), "howdy"))
        );
        assert_eq!(source.line(Line::from(2)), Some((BytePos::from(13), "")));
        assert_eq!(
            source.line(Line::from(3)),
            Some((BytePos::from(14), "hi萤"))
        );
        assert_eq!(
            source.line(Line::from(4)),
            Some((BytePos::from(20), "bloop"))
        );
        assert_eq!(source.line(Line::from(5)), Some((BytePos::from(26), "")));
        assert_eq!(source.line(Line::from(6)), None);
    }

    #[test]
    fn source_line_number_at_byte() {
        let source = test_source();

        assert_eq!(source.line_number_at_byte(BytePos::from(0)), Line::from(0));
        assert_eq!(source.line_number_at_byte(BytePos::from(6)), Line::from(0));
        assert_eq!(source.line_number_at_byte(BytePos::from(7)), Line::from(1));
        assert_eq!(source.line_number_at_byte(BytePos::from(8)), Line::from(1));

        assert_eq!(source.line_number_at_byte(BytePos::from(12)), Line::from(1));
        assert_eq!(source.line_number_at_byte(BytePos::from(13)), Line::from(2));
        assert_eq!(source.line_number_at_byte(BytePos::from(14)), Line::from(3));
        assert_eq!(source.line_number_at_byte(BytePos::from(15)), Line::from(3));

        assert_eq!(source.line_number_at_byte(BytePos::from(18)), Line::from(3));
        assert_eq!(source.line_number_at_byte(BytePos::from(19)), Line::from(3));
        assert_eq!(source.line_number_at_byte(BytePos::from(20)), Line::from(4));

        assert_eq!(
            source.line_number_at_byte(BytePos::from(400)),
            Line::from(5)
        );
    }

    #[test]
    fn source_location() {
        let source = test_source();

        assert_eq!(
            source.location(BytePos::from(0)),
            Some(Location {
                line: Line::from(0),
                column: Column::from(0),
                absolute: BytePos::from(0),
            })
        );

        assert_eq!(
            source.location(BytePos::from(3)),
            Some(Location {
                line: Line::from(0),
                column: Column::from(3),
                absolute: BytePos::from(3),
            })
        );

        assert_eq!(
            source.location(BytePos::from(16)),
            Some(Location {
                line: Line::from(3),
                column: Column::from(2),
                absolute: BytePos::from(16),
            })
        );

        assert_eq!(source.location(BytePos::from(400)), None);
    }

    #[test]
    fn source_location_end_of_source() {
        let source = test_source();
        assert_eq!(
            source.location(BytePos::from(source.src.len())),
            Some(Location {
                line: Line::from(5),
                column: Column::from(0),
                absolute: BytePos::from(source.src.len()),
            })
        );
    }
}
