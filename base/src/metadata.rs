use std::{collections::BTreeMap, fmt, sync::Arc};

use crate::{
    ast::Argument,
    symbol::{Symbol, SymbolRef},
};

pub trait MetadataEnv {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>>;
}

impl<'a, T: ?Sized + MetadataEnv> MetadataEnv for &'a T {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        (**self).get_metadata(id)
    }
}

impl MetadataEnv for () {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<Arc<Metadata>> {
        None
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub enum CommentType {
    Block,
    Line,
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Comment<S = String> {
    pub typ: CommentType,
    pub content: S,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Attribute {
    pub name: String,
    pub arguments: Option<String>,
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "#[{}", self.name)?;
        if let Some(arguments) = &self.arguments {
            write!(f, "({})", arguments)?;
        }
        write!(f, "]")
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct BaseMetadata {
    pub comment: Option<Comment>,
    pub attributes: Vec<Attribute>,
}

impl From<BaseMetadata> for Metadata {
    fn from(meta: BaseMetadata) -> Self {
        let BaseMetadata {
            comment,
            attributes,
        } = meta;
        Metadata {
            definition: None,
            comment,
            attributes,
            args: Vec::new(),
            module: BTreeMap::new(),
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Metadata {
    pub definition: Option<Symbol>,
    pub comment: Option<Comment>,
    pub attributes: Vec<Attribute>,
    pub args: Vec<Argument<Symbol>>,
    pub module: BTreeMap<String, Arc<Metadata>>,
}

impl Metadata {
    pub fn has_data(&self) -> bool {
        self.definition.is_some()
            || self.comment.is_some()
            || !self.module.is_empty()
            || !self.attributes.is_empty()
    }

    pub fn merge(mut self, other: Metadata) -> Metadata {
        self.merge_with(other);
        self
    }

    pub fn merge_with(&mut self, other: Metadata) {
        if other.definition.is_some() {
            self.definition = other.definition;
        }
        if self.comment.is_none() {
            self.comment = other.comment;
        }
        for (key, value) in other.module {
            use std::collections::btree_map::Entry;
            match self.module.entry(key) {
                Entry::Vacant(entry) => {
                    entry.insert(value);
                }
                Entry::Occupied(entry) => Arc::make_mut(entry.into_mut()).merge_with_ref(&value),
            }
        }
        self.attributes.extend(other.attributes);
        if self.args.is_empty() {
            self.args = other.args;
        }
    }

    pub fn merge_ref(mut self, other: &Metadata) -> Self {
        self.merge_with_ref(other);
        self
    }

    pub fn merge_with_ref(&mut self, other: &Metadata) {
        if other.definition.is_some() {
            self.definition = other.definition.clone();
        }
        if self.comment.is_none() {
            self.comment = other.comment.clone();
        }
        for (key, value) in &other.module {
            use std::collections::btree_map::Entry;
            match self.module.entry(key.clone()) {
                Entry::Vacant(entry) => {
                    entry.insert(value.clone());
                }
                Entry::Occupied(entry) => Arc::make_mut(entry.into_mut()).merge_with_ref(&value),
            }
        }
        self.attributes.extend(other.attributes.iter().cloned());
        if self.args.is_empty() {
            self.args = other.args.clone();
        }
    }

    pub fn merge_with_base_ref(&mut self, other: &BaseMetadata) {
        if self.comment.is_none() {
            self.comment = other.comment.clone();
        }
        self.attributes.extend(other.attributes.iter().cloned());
    }

    pub fn get_attribute(&self, name: &str) -> Option<&str> {
        self.attributes()
            .find(|attribute| attribute.name == name)
            .map(|t| t.arguments.as_ref().map_or("", |s| s))
    }

    pub fn attributes(&self) -> impl Iterator<Item = &Attribute> {
        self.attributes.iter()
    }
}

impl BaseMetadata {
    pub fn has_data(&self) -> bool {
        self.comment.is_some() || !self.attributes.is_empty()
    }

    pub fn get_attribute(&self, name: &str) -> Option<&str> {
        self.attributes()
            .find(|attribute| attribute.name == name)
            .map(|t| t.arguments.as_ref().map_or("", |s| s))
    }

    pub fn attributes(&self) -> impl Iterator<Item = &Attribute> {
        self.attributes.iter()
    }
}
