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

    pub fn get_attribute(&self, attribute: &str) -> Option<&str> {
        self.attributes()
            .find(|&(name, _)| name == attribute)
            .map(|t| t.1.unwrap_or(""))
    }

    pub fn attributes(&self) -> Attributes {
        attributes(self.comment.as_ref().map_or("", |s| s))
    }
}

pub struct Attributes<'a> {
    comment: ::std::str::Lines<'a>,
}

impl<'a> Iterator for Attributes<'a> {
    type Item = (&'a str, Option<&'a str>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(line) = self.comment.next() {
            if line.starts_with('@') {
                let mut split = line[1..].splitn(2, ' ');
                if let Some(x) = split.next().map(|key| (key, split.next())) {
                    return Some(x);
                }
            }
        }
        None
    }
}

pub fn attributes(comment: &str) -> Attributes {
    Attributes {
        comment: comment.lines(),
    }
}
