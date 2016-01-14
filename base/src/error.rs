use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

use ast;

#[derive(Debug, PartialEq)]
pub struct Errors<T> {
    pub errors: Vec<T>,
}

impl<T> Errors<T> {
    pub fn new() -> Errors<T> {
        Errors { errors: Vec::new() }
    }
    pub fn has_errors(&self) -> bool {
        self.errors.len() != 0
    }
    pub fn error(&mut self, t: T) {
        self.errors.push(t);
    }
}

impl<T: fmt::Display> fmt::Display for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.errors.iter() {
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
pub struct SourceContext<E> {
    context: String,
    error: ast::Spanned<E>,
}

#[derive(Debug)]
pub struct InFile<E> {
    file: String,
    error: Errors<SourceContext<E>>,
}

fn extract_context<E>(lines: &[&str], error: ast::Spanned<E>) -> SourceContext<E> {
    SourceContext {
        context: String::from(lines.get((error.span.start.row - 1) as usize).cloned().unwrap_or("N/A")),
        error: error,
    }
}

pub fn in_file<E>(file: String, contents: &str, error: Errors<ast::Spanned<E>>) -> InFile<E> {
    let lines: Vec<_> = contents.lines().collect();
    InFile {
        file: file,
        error: Errors {
            errors: error.errors.into_iter()
                                .map(|error| extract_context(&lines, error))
                                .collect()
        },
    }
}

impl<E: fmt::Display> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.error.errors.iter() {
            try!(write!(f, "{}:{}\n{}\n", self.file, error.error, error.context));
            for _ in 1..error.error.span.start.column {
                try!(write!(f, " "));
            }
            try!(write!(f, "^"));
            for _ in error.error.span.start.column..(error.error.span.end.column - 1) {
                try!(write!(f, "~"));
            }
        }
        Ok(())
    }
}

impl<T: fmt::Display + fmt::Debug + Any> StdError for InFile<T> {
    fn description(&self) -> &str {
        "Error in file"
    }
}
