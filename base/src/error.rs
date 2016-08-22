//! Module containing a few common error wrappers which allows more information to be saved for
//! later display to the user

use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

use pos::{BytePos, Spanned};
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

/// Error type which contains information of which file and where in the file the error occured
#[derive(Debug)]
pub struct InFile {
    message: String,
}

impl InFile {
    /// Creates a new `InFile` error which states that the error occured in `file` using the file
    /// contents in `source` to provide a context to the span.
    pub fn new<E: fmt::Display>(file: &str,
                                source: &Source,
                                error: Errors<Spanned<E, BytePos>>)
                                -> InFile {
        use std::fmt::Write;

        let mut message = String::new();

        for error in &error.errors {
            let start = source.location(error.span.start).unwrap();
            let end = source.location(error.span.end).unwrap();
            let (_, line) = source.line(start.line).unwrap();

            write!(message, "{}:{}\n{}\n", file, error.value, line).unwrap();

            for _ in 1..start.column.to_usize() {
                write!(message, " ").unwrap();
            }

            write!(message, "^").unwrap();

            for _ in start.column.to_usize()..(end.column.to_usize() - 1) {
                write!(message, "~").unwrap();
            }

            writeln!(message, "").unwrap();
        }

        InFile { message: message }
    }
}

impl fmt::Display for InFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.message.fmt(f)
    }
}

impl StdError for InFile {
    fn description(&self) -> &str {
        "Error in file"
    }
}
