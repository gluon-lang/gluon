//! Module containing a few common error wrappers which allows more information to be saved for
//! later display to the user
use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

use ast;

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
    context: String,
    error: ast::Spanned<E>,
}

fn extract_context<E>(lines: &[&str], error: ast::Spanned<E>) -> SourceContext<E> {
    SourceContext {
        context: String::from(lines.get((error.span.start.row - 1) as usize)
                                   .cloned()
                                   .unwrap_or("N/A")),
        error: error,
    }
}

/// Error type which contains information of which file and where in the file the error occured
#[derive(Debug)]
pub struct InFile<E> {
    file: String,
    error: Errors<SourceContext<E>>,
}

impl<E> InFile<E> {
    /// Creates a new `InFile` error which states that the error occured in `file` using the file
    /// contents in `contents` to provide a context to the span.
    pub fn new(file: String, contents: &str, error: Errors<ast::Spanned<E>>) -> InFile<E> {
        let lines: Vec<_> = contents.lines().collect();
        InFile {
            file: file,
            error: Errors {
                errors: error.errors
                             .into_iter()
                             .map(|error| extract_context(&lines, error))
                             .collect(),
            },
        }
    }
    pub fn errors(self) -> Errors<ast::Spanned<E>> {
        Errors { errors: self.error.errors.into_iter().map(|err| err.error).collect() }
    }
}

impl<E: fmt::Display> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.error.errors {
            try!(write!(f, "{}:{}\n{}\n", self.file, error.error, error.context));
            for _ in 1..error.error.span.start.column {
                try!(write!(f, " "));
            }
            try!(write!(f, "^"));
            for _ in error.error.span.start.column..(error.error.span.end.column - 1) {
                try!(write!(f, "~"));
            }
            try!(writeln!(f, ""));
        }
        Ok(())
    }
}

impl<T: fmt::Display + fmt::Debug + Any> StdError for InFile<T> {
    fn description(&self) -> &str {
        "Error in file"
    }
}
