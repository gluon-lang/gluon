use std::collections::BTreeMap;

use symbol::SymbolRef;

pub trait MetadataEnv {
    fn get_metadata(&self, id: &SymbolRef) -> Option<&Metadata>;
}

impl<'a, T: ?Sized + MetadataEnv> MetadataEnv for &'a T {
    fn get_metadata(&self, id: &SymbolRef) -> Option<&Metadata> {
        (**self).get_metadata(id)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Metadata {
    pub comment: Option<String>,
    pub module: BTreeMap<String, Metadata>,
}

impl Metadata {
    pub fn has_data(&self) -> bool {
        self.comment.is_some() || !self.module.is_empty()
    }

    pub fn merge(mut self, other: Metadata) -> Metadata {
        if self.comment.is_none() {
            self.comment = other.comment;
        }
        if self.module.is_empty() {
            self.module = other.module;
        }
        self
    }
}
