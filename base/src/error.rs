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

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::{
    pos::{BytePos, Spanned},
    source::FileId,
};

/// An error type which can represent multiple errors.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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

    pub fn drain(
        &mut self,
        range: impl std::ops::RangeBounds<usize>,
    ) -> impl Iterator<Item = T> + '_ {
        self.errors.drain(range)
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
        Errors { errors }
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
    source: crate::source::CodeMap,
    error: Errors<Spanned<E, BytePos>>,
}

impl<E> Eq for InFile<E> where E: Eq {}

impl<E> PartialEq for InFile<E>
where
    E: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.error == other.error
    }
}

impl<E> std::hash::Hash for InFile<E>
where
    E: std::hash::Hash,
{
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.error.hash(state)
    }
}

impl<E: fmt::Display> InFile<E> {
    /// Creates a new `InFile` error which states that the error occurred in `file` using the file
    /// contents in `source` to provide a context to the span.
    pub fn new(source: crate::source::CodeMap, error: Errors<Spanned<E, BytePos>>) -> InFile<E> {
        let err = InFile { source, error };
        // Verify that the source name can be accessed
        debug_assert!({
            err.source_name();
            true
        });
        err
    }

    pub fn source_name(&self) -> &str {
        self.source
            .get(self.error[0].span.start())
            .unwrap_or_else(|| {
                panic!(
                    "Source file does not exist in associated code map. Error: {}",
                    self.error
                )
            })
            .name()
    }

    pub fn source(&self) -> &crate::source::CodeMap {
        &self.source
    }

    pub fn errors(&self) -> &Errors<Spanned<E, BytePos>> {
        &self.error
    }

    pub fn into_errors(self) -> Errors<Spanned<E, BytePos>> {
        self.error
    }

    pub fn emit_string(&self) -> io::Result<String>
    where
        E: AsDiagnostic,
    {
        let mut output = Vec::new();
        self.emit(&mut ::codespan_reporting::term::termcolor::NoColor::new(
            &mut output,
        ))?;
        Ok(String::from_utf8(output).unwrap())
    }

    pub fn emit(
        &self,
        writer: &mut dyn ::codespan_reporting::term::termcolor::WriteColor,
    ) -> io::Result<()>
    where
        E: AsDiagnostic,
    {
        let iter = self
            .error
            .iter()
            .map(|error| error.as_diagnostic(&self.source))
            .enumerate();
        for (i, diagnostic) in iter {
            if i != 0 {
                writeln!(writer)?;
            }
            ::codespan_reporting::term::emit(
                &mut *writer,
                &Default::default(),
                &self.source,
                &diagnostic,
            )?;
        }
        Ok(())
    }
}

impl<E: fmt::Display + AsDiagnostic> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut buffer = Vec::new();
        {
            let mut writer = ::codespan_reporting::term::termcolor::NoColor::new(&mut buffer);

            self.emit(&mut writer).map_err(|_| fmt::Error)?;
        }

        write!(f, "{}", str::from_utf8(&buffer).unwrap())
    }
}

impl<E: fmt::Display + fmt::Debug + Any + AsDiagnostic> StdError for InFile<E> {
    fn description(&self) -> &str {
        "Error in file"
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
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
    fn as_diagnostic(&self, map: &crate::source::CodeMap) -> Diagnostic<FileId>;
}

impl<E> AsDiagnostic for Spanned<E, BytePos>
where
    E: AsDiagnostic,
{
    fn as_diagnostic(&self, map: &crate::source::CodeMap) -> Diagnostic<FileId> {
        let mut diagnostic = self.value.as_diagnostic(map);
        for label in &mut diagnostic.labels {
            if label.file_id == FileId::default() {
                label.file_id = self.span.start();
            }
            if label.range == (0..0) {
                if let Some(range) = self.span.to_range(map) {
                    label.range = range;
                }
            }
        }
        if diagnostic.labels.is_empty() {
            if let Some(range) = self.span.to_range(map) {
                diagnostic
                    .labels
                    .push(Label::primary(self.span.start(), range));
            }
        }
        diagnostic
    }
}

impl<E, H> AsDiagnostic for Help<E, H>
where
    E: AsDiagnostic,
    H: fmt::Display,
{
    fn as_diagnostic(&self, map: &crate::source::CodeMap) -> Diagnostic<FileId> {
        let mut diagnostic = self.error.as_diagnostic(map);
        if let Some(ref help) = self.help {
            diagnostic.labels.push(
                Label::secondary(
                    diagnostic
                        .labels
                        .last()
                        .map(|label| label.file_id)
                        .unwrap_or_default(),
                    0..0,
                )
                .with_message(help.to_string()),
            );
        }
        diagnostic
    }
}

impl AsDiagnostic for Box<dyn ::std::error::Error + Send + Sync> {
    fn as_diagnostic(&self, _map: &crate::source::CodeMap) -> Diagnostic<FileId> {
        Diagnostic::error().with_message(self.to_string())
    }
}

pub type SalvageResult<T, E> = std::result::Result<T, Salvage<T, E>>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Salvage<T, E> {
    pub value: Option<T>,
    pub error: E,
}

impl<T, E> fmt::Display for Salvage<T, E>
where
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl<T, E> Salvage<T, E> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Salvage<U, E> {
        Salvage {
            value: self.value.map(f),
            error: self.error,
        }
    }

    pub fn map_err<U>(self, f: impl FnOnce(E) -> U) -> Salvage<T, U> {
        Salvage {
            value: self.value,
            error: f(self.error),
        }
    }

    pub fn get_value(self) -> std::result::Result<T, E> {
        self.value.ok_or(self.error)
    }

    pub fn err_into<F>(self) -> Salvage<T, F>
    where
        F: From<E>,
    {
        let Salvage { value, error } = self;
        Salvage {
            value,
            error: error.into(),
        }
    }
}

impl<T, E> From<E> for Salvage<T, E> {
    fn from(error: E) -> Self {
        Salvage { value: None, error }
    }
}

impl<T, E> From<Salvage<T, InFile<E>>> for InFile<E> {
    fn from(s: Salvage<T, InFile<E>>) -> Self {
        s.error
    }
}
