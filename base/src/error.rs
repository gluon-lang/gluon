//! Module containing a few common error wrappers which allows more information to be saved for
//! later display to the user

use std::any::Any;
use std::error::Error as StdError;
use std::fmt;
use std::io;
use std::iter::{Extend, FromIterator};
use std::ops::{Index, IndexMut};
use std::slice;
use std::str;
use std::vec;

use codespan_reporting::{Diagnostic, Label};

use pos::{BytePos, Span, Spanned};

/// An error type which can represent multiple errors.
#[derive(Clone, Debug, PartialEq)]
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

    pub fn iter(&self) -> slice::Iter<T> {
        self.errors.iter()
    }
}

impl<T> Index<usize> for Errors<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        &self.errors[index]
    }
}

impl<T> IndexMut<usize> for Errors<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.errors[index]
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

/// Error type which contains information of which file and where in the file the error occurred
#[derive(Clone, Debug)]
pub struct InFile<E> {
    source: ::codespan::CodeMap,
    error: Errors<Spanned<E, BytePos>>,
}

impl<E> PartialEq for InFile<E>
where
    E: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.error == other.error
    }
}

impl<E: fmt::Display> InFile<E> {
    /// Creates a new `InFile` error which states that the error occurred in `file` using the file
    /// contents in `source` to provide a context to the span.
    pub fn new(source: ::codespan::CodeMap, error: Errors<Spanned<E, BytePos>>) -> InFile<E> {
        let err = InFile { source, error };
        // Verify that the source name can be accessed
        debug_assert!({
            err.source_name();
            true
        });
        err
    }

    pub fn source_name(&self) -> &::codespan::FileName {
        self.source
            .find_file(self.error[0].span.start())
            .expect("Source file does not exist in associated code map")
            .name()
    }

    pub fn errors(self) -> Errors<Spanned<E, BytePos>> {
        self.error
    }

    pub fn emit_string(&self, code_map: &::codespan::CodeMap) -> io::Result<String>
    where
        E: AsDiagnostic,
    {
        let mut output = Vec::new();
        self.emit(
            &mut ::codespan_reporting::termcolor::NoColor::new(&mut output),
            code_map,
        )?;
        Ok(String::from_utf8(output).unwrap())
    }

    pub fn emit<W>(&self, writer: &mut W, code_map: &::codespan::CodeMap) -> io::Result<()>
    where
        W: ?Sized + ::codespan_reporting::termcolor::WriteColor,
        E: AsDiagnostic,
    {
        let iter = self
            .error
            .iter()
            .map(AsDiagnostic::as_diagnostic)
            .enumerate();
        for (i, diagnostic) in iter {
            if i != 0 {
                writeln!(writer)?;
            }
            ::codespan_reporting::emit(&mut *writer, &code_map, &diagnostic)?;
        }
        Ok(())
    }
}

impl<E: fmt::Display + AsDiagnostic> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buffer = Vec::new();
        {
            let mut writer = ::codespan_reporting::termcolor::NoColor::new(&mut buffer);

            self.emit(&mut writer, &self.source)
                .map_err(|_| fmt::Error)?;
        }

        write!(f, "{}", str::from_utf8(&buffer).unwrap())
    }
}

impl<E: fmt::Display + fmt::Debug + Any + AsDiagnostic> StdError for InFile<E> {
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

pub trait AsDiagnostic {
    fn as_diagnostic(&self) -> Diagnostic;
}

impl<E> AsDiagnostic for Spanned<E, BytePos>
where
    E: AsDiagnostic,
{
    fn as_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = self.value.as_diagnostic();
        diagnostic.labels.insert(0, Label::new_primary(self.span));
        diagnostic
    }
}

impl<E, H> AsDiagnostic for Help<E, H>
where
    E: AsDiagnostic,
    H: fmt::Display,
{
    fn as_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = self.error.as_diagnostic();
        if let Some(ref help) = self.help {
            diagnostic.labels.push(
                Label::new_secondary(Span::new(BytePos::none(), BytePos::none()))
                    .with_message(help.to_string()),
            );
        }
        diagnostic
    }
}

impl AsDiagnostic for Box<::std::error::Error + Send + Sync> {
    fn as_diagnostic(&self) -> Diagnostic {
        Diagnostic::new_error(self.to_string())
    }
}
