use std::any::Any;
use std::error::Error as StdError;
use std::fmt;

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
pub struct InFile<E> {
    file: String,
    error: Errors<E>,
}

pub fn in_file<E>(file: String, error: Errors<E>) -> InFile<E> {
    InFile {
        file: file,
        error: error,
    }
}

impl<E: fmt::Display> fmt::Display for InFile<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.error.errors.iter() {
            try!(write!(f, "{}:{}\n", self.file, error));
        }
        Ok(())
    }
}

impl<T: fmt::Display + fmt::Debug + Any> StdError for InFile<T> {
    fn description(&self) -> &str {
        "Error in file"
    }
}
