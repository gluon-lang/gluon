use base::ast::{DisplayEnv, IdentEnv};
use std::marker::PhantomData;

pub struct MockEnv<T>(PhantomData<T>);

impl<T> MockEnv<T> {
    pub fn new() -> MockEnv<T> {
        MockEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for MockEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<T> IdentEnv for MockEnv<T>
    where T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}
