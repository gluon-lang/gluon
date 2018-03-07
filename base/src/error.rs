//! Module containing a few common error wrappers which allows more information to be saved for
//! later display to the user

use std::any::Any;
use std::error::Error as StdError;
use std::fmt;
use std::iter::{Extend, FromIterator};
use std::slice;
use std::vec;

use pos::{BytePos, Location, Span, Spanned, spanned2};
use source::Source;

/// An error type which can represent multiple errors.
#[derive(Debug, PartialEq)]
pub struct Errors<T> {
    errors: Vec<T>,
}

impl<T> Default for Errors<T> {
    fn default() -> Self {
        Errors::new()
    }
}

impl<T> Errors<T> {
    /// Creates a new, empty `Errors` instance.
    pub fn new() -> Errors<T> {
        Errors::from(Vec::new())
    }

    /// Returns true if `self` contains any errors
    pub fn has_errors(&self) -> bool {
        !self.is_empty()
    }

    /// The number of errors in the error list
    pub fn len(&self) -> usize {
        self.errors.len()
    }

    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    /// Adds an error to `self`
    pub fn push(&mut self, t: T) {
        self.errors.push(t);
    }

    /// Pops and error off the error list
    pub fn pop(&mut self) -> Option<T> {
        self.errors.pop()
    }
}

impl<T> Extend<T> for Errors<T> {
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, iter: Iter) {
        self.errors.extend(iter);
    }
}

impl<T> From<Vec<T>> for Errors<T> {
    fn from(errors: Vec<T>) -> Errors<T> {
        Errors { errors: errors }
    }
}

impl<T> FromIterator<T> for Errors<T> {
    fn from_iter<Iter: IntoIterator<Item = T>>(iter: Iter) -> Errors<T> {
        Errors {
            errors: iter.into_iter().collect(),
        }
    }
}

impl<T> Into<Vec<T>> for Errors<T> {
    fn into(self) -> Vec<T> {
        self.errors
    }
}

impl<T> IntoIterator for Errors<T> {
    type Item = T;

    type IntoIter = vec::IntoIter<T>;

    fn into_iter(self) -> vec::IntoIter<T> {
        self.errors.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Errors<T> {
    type Item = &'a T;

    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> slice::Iter<'a, T> {
        self.errors.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Errors<T> {
    type Item = &'a mut T;

    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.errors.iter_mut()
    }
}

impl<T: fmt::Display> fmt::Display for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, error) in self.errors.iter().enumerate() {
            write!(f, "{}", error)?;
            // Errors are assumed to not have a newline at the end so we add one to keep errors on
            // separate lines and one to space them out
            if i + 1 != self.errors.len() {
                writeln!(f)?;
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

impl<T: fmt::Display + fmt::Debug + Any> StdError for Errors<T> {
    fn description(&self) -> &str {
        "Errors"
    }
}

#[derive(Debug, PartialEq)]
struct SourceContext<E> {
    line: String,
    error: Spanned<E, Location>,
}

impl<E> SourceContext<E>
where
    E: fmt::Display,
{
    fn new(source: &Source, error: Spanned<E, BytePos>) -> SourceContext<E> {
        debug_assert!(
            error.span.start.to_usize() <= source.src().len()
                && error.span.end.to_usize() <= source.src().len(),
            "{}",
            error,
        );

        let start = source.location(error.span.start).unwrap();
        let end = source.location(error.span.end).unwrap();
        let (_, line) = source.line_at_byte(error.span.start).unwrap();

        SourceContext {
            line: line.to_string(),
            error: spanned2(start, end, error.value),
        }
    }
}

/// Error type which contains information of which file and where in the file the error occurred
#[derive(Debug, PartialEq)]
pub struct InFile<E> {
    pub source_name: String,
    error: Errors<SourceContext<E>>,
}

impl<E: fmt::Display> InFile<E> {
    /// Creates a new `InFile` error which states that the error occurred in `file` using the file
    /// contents in `source` to provide a context to the span.
    pub fn new(source_name: &str, source: &str, error: Errors<Spanned<E, BytePos>>) -> InFile<E> {
        let source = Source::new(source);

        InFile {
            source_name: source_name.to_string(),
            error: Errors {
                errors: error
                    .errors
                    .into_iter()
                    .map(|error| SourceContext::new(&source, error))
                    .collect(),
            },
        }
    }

    pub fn errors(self) -> Errors<Spanned<E, Location>> {
        Errors {
            errors: self.error.errors.into_iter().map(|err| err.error).collect(),
        }
    }
}

impl<E: fmt::Display> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.error.errors {
            let Span { start, end, .. } = error.error.span;

            write!(f, "{}:{}\n{}\n", self.source_name, error.error, error.line)?;

            for _ in 0..start.column.to_usize() {
                write!(f, " ")?;
            }

            write!(f, "^")?;
            for _ in (start.column.to_usize() + 1)..end.column.to_usize() {
                write!(f, "~")?;
            }

            writeln!(f, "")?;
        }
        Ok(())
    }
}

impl<E: fmt::Display + fmt::Debug + Any> StdError for InFile<E> {
    fn description(&self) -> &str {
        "Error in file"
    }
}

#[derive(Debug, PartialEq)]
pub struct Help<E, H> {
    pub error: E,
    pub help: Option<H>,
}

impl<E, H> fmt::Display for Help<E, H>
where
    E: fmt::Display,
    H: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.error)?;
        if let Some(ref help) = self.help {
            writeln!(f)?;
            write!(f, "help: {}", help)?;
        }
        Ok(())
    }
}

impl<E, H> From<E> for Help<E, H> {
    fn from(error: E) -> Help<E, H> {
        Help { error, help: None }
    }
}
