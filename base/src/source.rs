use pos::{BytePos, Column, Line, Location};

#[derive(Clone, Debug)]
pub struct Source<'a> {
    src: &'a str,
    /// The starting byte position of each line in `src`
    lines: Vec<BytePos>,
}

impl<'a> Source<'a> {
    pub fn new(src: &str) -> Source {
        use std::iter;

        let lines = {
            let input_indices = src.as_bytes()
                .iter()
                .enumerate()
                .filter(|&(_, &b)| b == b'\n')
                .map(|(i, _)| BytePos::from(i + 1)); // index of first char in the line

            iter::once(BytePos::from(0))
                .chain(input_indices)
                .collect()
        };

        Source {
            src: src,
            lines: lines,
        }
    }

    pub fn src(&self) -> &str {
        &self.src
    }

    pub fn line(&self, line_number: Line) -> Option<(BytePos, &str)> {
        let line_number = line_number.to_usize();

        self.lines.get(line_number).map(|&start| {
            let line = match self.lines.get(line_number + 1) {
                Some(end) => &self.src[start.to_usize()..end.to_usize() - 1], // Skip '\n'
                None => &self.src[start.to_usize()..],
            };

            (start, line)
        })
    }

    pub fn line_at_byte(&self, byte: BytePos) -> Option<(BytePos, &str)> {
        let line_number = self.line_number_at_byte(byte);
        self.line(line_number)
    }

    pub fn line_number_at_byte(&self, byte: BytePos) -> Line {
        let num_lines = self.lines.len();

        Line::from((0..num_lines)
            .filter(|&i| self.lines[i] > byte)
            .map(|i| i - 1)
            .next()
            .unwrap_or(num_lines - 1))
    }

    pub fn location(&self, byte: BytePos) -> Option<Location> {
        let line_index = self.line_number_at_byte(byte);

        self.line(line_index).and_then(|(line_byte, line)| {
            let mut column_index = Column::from(0);

            for (i, (next_byte, _)) in line.char_indices().enumerate() {
                column_index = Column::from(i);

                let curr_byte = line_byte + BytePos::from(next_byte);

                if curr_byte == byte {
                    return Some(Location {
                        line: line_index,
                        column: column_index,
                        absolute: byte,
                    });
                }
            }

            // Handle the case where `byte` is equal to the source's length
            if byte == line_byte + BytePos::from(line.len()) {
                Some(Location {
                    line: line_index,
                    column: column_index,
                    absolute: byte,
                })
            } else {
                None
            }
        })
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

        assert_eq!(source.line(Line::from(0)),
                   Some((BytePos::from(0), "hello!")));
        assert_eq!(source.line(Line::from(1)),
                   Some((BytePos::from(7), "howdy")));
        assert_eq!(source.line(Line::from(2)), Some((BytePos::from(13), "")));
        assert_eq!(source.line(Line::from(3)),
                   Some((BytePos::from(14), "hi萤")));
        assert_eq!(source.line(Line::from(4)),
                   Some((BytePos::from(20), "bloop")));
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

        assert_eq!(source.line_number_at_byte(BytePos::from(400)),
                   Line::from(5));
    }

    #[test]
    fn source_location() {
        let source = test_source();

        assert_eq!(source.location(BytePos::from(0)),
                   Some(Location {
                       line: Line::from(0),
                       column: Column::from(0),
                       absolute: BytePos::from(0),
                   }));

        assert_eq!(source.location(BytePos::from(3)),
                   Some(Location {
                       line: Line::from(0),
                       column: Column::from(3),
                       absolute: BytePos::from(3),
                   }));

        assert_eq!(source.location(BytePos::from(16)),
                   Some(Location {
                       line: Line::from(3),
                       column: Column::from(2),
                       absolute: BytePos::from(16),
                   }));

        assert_eq!(source.location(BytePos::from(400)), None);
    }

    #[test]
    fn source_location_end_of_source() {
        let source = test_source();
        assert_eq!(source.location(BytePos::from(source.src.len())),
                   Some(Location {
                       line: Line::from(5),
                       column: Column::from(0),
                       absolute: BytePos::from(source.src.len()),
                   }));
    }
}
