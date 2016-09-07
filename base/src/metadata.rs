use std::collections::BTreeMap;

use symbol::Symbol;

pub trait MetadataEnv {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata>;
}

impl<'a, T: ?Sized + MetadataEnv> MetadataEnv for &'a T {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata> {
        (**self).get_metadata(id)
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
