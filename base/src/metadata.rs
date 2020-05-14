use std::{collections::BTreeMap, fmt, mem, sync::Arc};

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

#[derive(Debug, Default, Eq, PartialEq, Hash, gluon_codegen::AstClone)]
pub struct BaseMetadata<'ast> {
    pub metadata: Option<&'ast mut Metadata>,
}

impl From<BaseMetadata<'_>> for Metadata {
    fn from(meta: BaseMetadata<'_>) -> Self {
        meta.metadata.map(|m| m.clone()).unwrap_or_default()
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

    pub fn merge_with_base(mut self, other: &BaseMetadata<'_>) -> Self {
        self.merge_with_base_ref(other);
        self
    }

    pub fn merge_with_base_ref(&mut self, other: &BaseMetadata<'_>) {
        if let Some(other) = &other.metadata {
            self.merge_with_ref(other);
        }
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

impl<'ast> BaseMetadata<'ast> {
    pub fn has_data(&self) -> bool {
        self.metadata.is_some()
    }

    pub fn merge(&mut self, metadata: BaseMetadata<'ast>) {
        match &mut self.metadata {
            Some(self_) => {
                if let Some(metadata) = metadata.metadata {
                    self_.merge_with(mem::take(metadata));
                }
            }
            None => *self = metadata,
        }
    }

    pub fn comment(&self) -> Option<&Comment> {
        self.metadata.as_ref().and_then(|m| m.comment.as_ref())
    }

    pub fn get_attribute(&self, name: &str) -> Option<&str> {
        self.attributes()
            .find(|attribute| attribute.name == name)
            .map(|t| t.arguments.as_ref().map_or("", |s| s))
    }

    pub fn attributes(&self) -> impl Iterator<Item = &Attribute> {
        self.metadata.iter().flat_map(|m| m.attributes())
    }

    pub fn to_metadata(&self) -> Metadata {
        self.metadata
            .as_ref()
            .map(|m| (**m).clone())
            .unwrap_or_default()
    }
}
