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

impl MetadataEnv for () {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<&Metadata> {
        None
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub enum CommentType {
    Block,
    Line,
}

#[derive(Clone, Eq, PartialEq, Debug)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Comment {
    pub typ: CommentType,
    pub content: String,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Attribute {
    pub name: String,
    pub arguments: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Metadata {
    pub comment: Option<Comment>,
    pub attributes: Vec<Attribute>,
    pub module: BTreeMap<String, Metadata>,
}

impl Metadata {
    pub fn has_data(&self) -> bool {
        self.comment.is_some() || !self.module.is_empty() || !self.attributes.is_empty()
    }

    pub fn merge(mut self, other: Metadata) -> Metadata {
        self.merge_with(other);
        self
    }

    pub fn merge_with(&mut self, other: Metadata) {
        if self.comment.is_none() {
            self.comment = other.comment;
        }
        if self.module.is_empty() {
            self.module = other.module;
        }
        self.attributes.extend(other.attributes);
    }

    pub fn get_attribute(&self, name: &str) -> Option<&str> {
        self.attributes()
            .find(|attribute| attribute.name == name)
            .map(|t| t.arguments.as_ref().map_or("", |s| s))
    }

    // TODO Use impl Iterator
    pub fn attributes<'a>(&'a self) -> Box<Iterator<Item = &'a Attribute> + 'a> {
        Box::new(self.attributes.iter())
    }
}
