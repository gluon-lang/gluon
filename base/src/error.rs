//! Module containing a few common error wrappers which allows more information to be saved for
//! later display to the user

use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

use pos::{BytePos, Location, Span, Spanned, spanned2};
use source::Source;

/// An error type which can represent multiple errors.
#[derive(Debug, PartialEq)]
pub struct Errors<T> {
    pub errors: Vec<T>,
}

impl<T> Errors<T> {
    /// Creates a new, empty `Errors` instance.
    pub fn new() -> Errors<T> {
        Errors { errors: Vec::new() }
    }

    /// Returns true if `self` contains any errors
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Adds an error to `self`
    pub fn error(&mut self, t: T) {
        self.errors.push(t);
    }
}

impl<T: fmt::Display> fmt::Display for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.errors {
            try!(write!(f, "{}\n", error));
        }
        Ok(())
    }
}

impl<T: fmt::Display + fmt::Debug + Any> StdError for Errors<T> {
    fn description(&self) -> &str {
        "Errors"
    }
}

#[derive(Debug)]
struct SourceContext<E> {
    line: String,
    error: Spanned<E, Location>,
}

impl<E> SourceContext<E> {
    fn new(source: &Source, error: Spanned<E, BytePos>) -> SourceContext<E> {
        let start = source.location(error.span.start).unwrap();
        let end = source.location(error.span.end).unwrap();
        let (_, line) = source.line_at_byte(error.span.start).unwrap();

        SourceContext {
            line: line.to_string(),
            error: spanned2(start, end, error.value),
        }
    }
}

/// Error type which contains information of which file and where in the file the error occured
#[derive(Debug)]
pub struct InFile<E> {
    pub source_name: String,
    error: Errors<SourceContext<E>>,
}

impl<E: fmt::Display> InFile<E> {
    /// Creates a new `InFile` error which states that the error occured in `file` using the file
    /// contents in `source` to provide a context to the span.
    pub fn new(source_name: &str, source: &str, error: Errors<Spanned<E, BytePos>>) -> InFile<E> {
        let source = Source::new(source);

        InFile {
            source_name: source_name.to_string(),
            error: Errors {
                errors: error.errors
                    .into_iter()
                    .map(|error| SourceContext::new(&source, error))
                    .collect(),
            },
        }
    }

    pub fn errors(self) -> Errors<Spanned<E, Location>> {
        Errors { errors: self.error.errors.into_iter().map(|err| err.error).collect() }
    }
}

impl<E: fmt::Display> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.error.errors {
            let Span { start, end, .. } = error.error.span;

            try!(write!(f, "{}:{}\n{}\n", self.source_name, error.error, error.line));

            for _ in 0..start.column.to_usize() {
                try!(write!(f, " "));
            }

            try!(write!(f, "^"));
            for _ in (start.column.to_usize() + 1)..end.column.to_usize() {
                try!(write!(f, "~"));
            }

            try!(writeln!(f, ""));
        }
        Ok(())
    }
}

impl<E: fmt::Display + fmt::Debug + Any> StdError for InFile<E> {
    fn description(&self) -> &str {
        "Error in file"
    }
}
