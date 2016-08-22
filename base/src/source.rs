use pos::{BytePos, CharPos, Location};

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

            iter::once(BytePos(0))
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

    pub fn line(&self, line_number: u32) -> Option<(BytePos, &str)> {
        let line_number = line_number as usize;

        if line_number == 0 {
            return None;
        }

        self.lines.get(line_number - 1).map(|&start| {
            let line = match self.lines.get(line_number) {
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

    pub fn line_number_at_byte(&self, byte: BytePos) -> u32 {
        let num_lines = self.lines.len();

        ((0..num_lines)
            .filter(|&i| self.lines[i] > byte)
            .map(|i| i - 1)
            .next()
            .unwrap_or(num_lines - 1) + 1) as u32
    }

    pub fn location(&self, byte: BytePos) -> Option<Location> {
        let line_number = self.line_number_at_byte(byte);

        self.line(line_number).and_then(|(line_byte, line)| {
            for (col, (next_byte, _)) in line.char_indices().enumerate() {
                let curr_byte = line_byte + BytePos::from(next_byte);

                if curr_byte == byte {
                    return Some(Location {
                        line: line_number as u32,
                        column: CharPos(col + 1),
                        absolute: byte,
                    });
                }
            }
            None
        })
    }
}

#[cfg(test)]
mod tests {
    use pos::{BytePos, CharPos, Location};

    use super::Source;

    fn test_source() -> Source<'static> {
        Source::new("hello!\nhowdy\n\nhi萤\nbloop\n")
    }

    #[test]
    fn source_line() {
        let source = test_source();

        assert_eq!(source.line(0), None);
        assert_eq!(source.line(1), Some((BytePos(0), "hello!")));
        assert_eq!(source.line(2), Some((BytePos(7), "howdy")));
        assert_eq!(source.line(3), Some((BytePos(13), "")));
        assert_eq!(source.line(4), Some((BytePos(14), "hi萤")));
        assert_eq!(source.line(5), Some((BytePos(20), "bloop")));
        assert_eq!(source.line(6), Some((BytePos(26), "")));
        assert_eq!(source.line(7), None);
    }

    #[test]
    fn source_line_number_at_byte() {
        assert_eq!(test_source().line_number_at_byte(BytePos(0)), 1);
        assert_eq!(test_source().line_number_at_byte(BytePos(3)), 1);
        assert_eq!(test_source().line_number_at_byte(BytePos(13)), 3);
        assert_eq!(test_source().line_number_at_byte(BytePos(18)), 4);
        assert_eq!(test_source().line_number_at_byte(BytePos(400)), 6);
    }

    #[test]
    fn source_location() {
        let source = test_source();

        assert_eq!(source.location(BytePos(0)),
                   Some(Location {
                       line: 1,
                       column: CharPos(1),
                       absolute: BytePos(0),
                   }));

        assert_eq!(source.location(BytePos(3)),
                   Some(Location {
                       line: 1,
                       column: CharPos(4),
                       absolute: BytePos(3),
                   }));

        assert_eq!(source.location(BytePos(16)),
                   Some(Location {
                       line: 4,
                       column: CharPos(3),
                       absolute: BytePos(16),
                   }));

        assert_eq!(source.location(BytePos(400)), None);
    }
}
