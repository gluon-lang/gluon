//! Module containing types and functions for mapping between byte indexes and line and column
//! locations
use std::{fmt, ops::Range, sync::Arc};

use itertools::Itertools;

use crate::pos::{ByteOffset, BytePos, Column, Line, Location, RawIndex, Span};

use codespan_reporting::files::{Files, SimpleFile};

pub type FileId = BytePos;

pub struct FileMap {
    file: SimpleFile<String, String>,
    span_start: FileId,
}

impl fmt::Debug for FileMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FileMap")
            .field("file", &self.file.source())
            .field("span", &self.span())
            .finish()
    }
}

impl FileMap {
    pub fn new(name: String, source: String) -> Self {
        Self {
            file: SimpleFile::new(name, source),
            span_start: BytePos(1),
        }
    }

    fn with_index(name: String, source: String, span_start: FileId) -> Self {
        FileMap {
            file: SimpleFile::new(name, source),
            span_start,
        }
    }

    fn from_usize(&self, pos: usize) -> BytePos {
        self.span_start + ByteOffset(pos as i64)
    }

    fn to_usize(&self, pos: BytePos) -> Option<usize> {
        if self.span().containment(pos) == std::cmp::Ordering::Equal {
            Some(pos.to_usize() - self.span_start.to_usize())
        } else {
            None
        }
    }

    pub fn span(&self) -> Span<BytePos> {
        Span::new(
            self.span_start,
            self.span_start + ByteOffset(self.src().len() as i64),
        )
    }

    pub fn source(&self) -> &str {
        self.file.source()
    }

    pub fn name(&self) -> &str {
        self.file.name()
    }
}

#[derive(Clone, Debug, Default)]
pub struct CodeMap {
    files: Vec<Arc<FileMap>>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_filemap(&mut self, filename: String, source: String) -> Arc<FileMap> {
        let start_index = self
            .files
            .last()
            .map(|file| file.span().end())
            .unwrap_or_default()
            + ByteOffset::from(1);
        let file_map = Arc::new(FileMap::with_index(filename, source, start_index));
        self.files.push(file_map.clone());
        file_map
    }

    pub fn to_usize(&self, pos: BytePos) -> Option<usize> {
        self.get(pos)?.to_usize(pos)
    }

    pub fn find_file(&self, file: &str) -> Option<&Arc<FileMap>> {
        self.files.iter().find(|file_map| file_map.name() == file)
    }

    pub fn get(&self, file_id: FileId) -> Option<&Arc<FileMap>> {
        let i = self.find_index(file_id)?;
        self.files.get(i)
    }

    pub fn update(&mut self, index: BytePos, src: String) -> Option<Arc<FileMap>> {
        self.find_index(index).map(|i| {
            let min = if i == 0 {
                BytePos(1)
            } else {
                self.files[i - 1].span().end() + ByteOffset(1)
            };
            let max = self
                .files
                .get(i + 1)
                .map_or(BytePos(RawIndex::max_value()), |file_map| {
                    file_map.span().start()
                })
                - ByteOffset(1);
            if src.len() <= (max - min).to_usize() {
                let start_index = self.files[i].span().start();
                let name = self.files[i].name().to_owned();
                let new_file = Arc::new(FileMap::with_index(name, src, start_index));
                self.files[i] = new_file.clone();
                new_file
            } else {
                let file = self.files.remove(i);
                match self
                    .files
                    .first()
                    .map(|file| file.span().start().to_usize() - 1)
                    .into_iter()
                    .chain(
                        self.files
                            .iter()
                            .tuple_windows()
                            .map(|(x, y)| (y.span().start() - x.span().end()).to_usize() - 1),
                    )
                    .position(|size| size >= src.len() + 1)
                {
                    Some(j) => {
                        let start_index = if j == 0 {
                            BytePos(1)
                        } else {
                            self.files[j - 1].span().end() + ByteOffset(1)
                        };
                        let new_file = Arc::new(FileMap::with_index(
                            file.name().to_owned(),
                            src,
                            start_index,
                        ));
                        self.files.insert(j, new_file.clone());
                        new_file
                    }
                    None => self.add_filemap(file.name().to_owned(), src),
                }
            }
        })
    }

    fn find_index(&self, index: BytePos) -> Option<usize> {
        use std::cmp::Ordering;
        self.files
            .binary_search_by(|file| {
                let span = file.span();
                match () {
                    () if span.start() > index => Ordering::Greater,
                    () if span.end() < index => Ordering::Less,
                    () => Ordering::Equal,
                }
            })
            .ok()
    }
}

impl<'a> Files<'a> for FileMap {
    type FileId = ();
    type Name = String;
    type Source = &'a str;

    fn name(&self, _file_id: Self::FileId) -> Option<Self::Name> {
        Some(self.file.name().clone())
    }

    fn source(&self, _file_id: Self::FileId) -> Option<&str> {
        Some(self.file.source())
    }

    fn line_index(&self, file_id: Self::FileId, byte_index: usize) -> Option<usize> {
        self.file.line_index(file_id, byte_index)
    }

    fn line_range(&self, file_id: Self::FileId, line_index: usize) -> Option<Range<usize>> {
        self.file.line_range(file_id, line_index)
    }
}

impl<'a> Files<'a> for CodeMap {
    type FileId = FileId;
    type Name = String;
    type Source = &'a str;

    fn name(&self, file_id: FileId) -> Option<Self::Name> {
        Some(self.get(file_id)?.name().to_owned())
    }

    fn source(&self, file_id: FileId) -> Option<&str> {
        Some(self.get(file_id)?.source())
    }

    fn line_index(&self, file_id: FileId, byte_index: usize) -> Option<usize> {
        self.get(file_id)?.line_index((), byte_index)
    }

    fn line_range(&self, file_id: FileId, line_index: usize) -> Option<Range<usize>> {
        self.get(file_id)?.line_range((), line_index)
    }
}

pub trait Source {
    fn new(s: &str) -> Self
    where
        Self: Sized;

    fn location(&self, byte: BytePos) -> Option<Location>;

    fn span(&self) -> Span<BytePos>;

    fn src(&self) -> &str;

    fn src_slice(&self, span: Span<BytePos>) -> &str;

    fn byte_index(&self, line: Line, column: Column) -> Option<BytePos>;

    fn line_number_at_byte(&self, pos: BytePos) -> Option<Line>;

    /// Returns the starting position of any comments and whitespace before `end`
    fn comment_start_before(&self, end: BytePos) -> BytePos;

    fn comments_between(&self, span: Span<BytePos>) -> CommentIter;
}

impl Source for FileMap {
    fn new(s: &str) -> Self
    where
        Self: Sized,
    {
        Self::new("test".into(), s.into())
    }

    fn span(&self) -> Span<BytePos> {
        FileMap::span(self)
    }

    fn src(&self) -> &str {
        self.source()
    }

    fn src_slice(&self, span: Span<BytePos>) -> &str {
        &self.src()[self.to_usize(span.start()).unwrap()..self.to_usize(span.end()).unwrap()]
    }

    fn byte_index(&self, line: Line, column: Column) -> Option<BytePos> {
        let range = self.line_range((), line.to_usize())?;
        Some(self.from_usize(range.start + column.to_usize()))
    }

    fn line_number_at_byte(&self, pos: BytePos) -> Option<Line> {
        self.line_index((), self.to_usize(pos)?)
            .map(|l| Line(l as u32))
    }

    /// Returns the line and column location of `byte`
    fn location(&self, byte: BytePos) -> Option<Location> {
        Files::location(self, (), self.to_usize(byte)?).map(|loc| Location {
            line: Line(loc.line_number as u32 - 1),
            column: Column(loc.column_number as u32 - 1),
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
            src: self.src_slice(span),
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

    fn byte_index(&self, _: Line, _: Column) -> Option<BytePos> {
        None
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
                .trim_end_matches(|c: char| c.is_whitespace() && c != '\n');
            if self.src.ends_with('\n') {
                let comment_line = self.src[..self.src.len() - 1].lines().next_back()?;
                let trimmed = comment_line.trim_start();

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
