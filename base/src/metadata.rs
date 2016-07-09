use std::collections::BTreeMap;

use symbol::Symbol;

pub trait MetadataEnv {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata>;
}

impl MetadataEnv for () {
    fn get_metadata(&self, _id: &Symbol) -> Option<&Metadata> {
        None
    }
}

impl<'a, T: ?Sized + MetadataEnv> MetadataEnv for &'a T {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata> {
        (**self).get_metadata(id)
    }
}

impl<T: MetadataEnv, U: MetadataEnv> MetadataEnv for (T, U) {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata> {
        let &(ref outer, ref inner) = self;
        inner.get_metadata(id)
            .or_else(|| outer.get_metadata(id))
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Metadata {
    pub comment: Option<String>,
    pub module: BTreeMap<String, Metadata>,
}

impl Metadata {
    pub fn has_data(&self) -> bool {
        self.comment.is_some() || !self.module.is_empty()
    }
}
