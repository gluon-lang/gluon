use base::fnv::FnvMap;

use interner::InternedStr;
use types::{VmTag, VmIndex};

pub struct FieldMap {
    /// Maps fields into a tag
    tags: FnvMap<Vec<InternedStr>, VmTag>,
    /// Maps the tag the record has and the field name onto the offset in the data
    fields: FnvMap<(VmTag, InternedStr), VmIndex>,
}

impl FieldMap {
    pub fn new() -> FieldMap {
        FieldMap {
            tags: FnvMap::default(),
            fields: FnvMap::default(),
        }
    }

    pub fn get_offset(&self, tag: VmTag, name: InternedStr) -> Option<VmIndex> {
        self.fields.get(&(tag, name)).cloned()
    }

    pub fn get_map(&mut self, fields: &[InternedStr]) -> VmTag {
        if let Some(tag) = self.tags.get(fields) {
            return *tag;
        }
        let tag = self.tags.len() as VmTag;
        self.tags.insert(fields.to_owned(), tag);
        for (offset, field) in fields.iter().enumerate() {
            self.fields.insert((tag, *field), offset as VmIndex);
        }
        tag
    }
}
