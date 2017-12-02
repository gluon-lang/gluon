use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use Result;
use base::fnv::FnvMap;

use gc::{Gc, Traverseable};
use value::GcStr;

/// Interned strings which allow for fast equality checks and hashing
#[derive(Copy, Clone, Eq)]
pub struct InternedStr(GcStr);

impl PartialEq<InternedStr> for InternedStr {
    fn eq(&self, other: &InternedStr) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl<'a> PartialEq<&'a str> for InternedStr {
    fn eq(&self, other: &&'a str) -> bool {
        **self == **other
    }
}

impl PartialOrd for InternedStr {
    fn partial_cmp(&self, other: &InternedStr) -> Option<Ordering> {
        self.as_ptr().partial_cmp(&other.as_ptr())
    }
}

impl Ord for InternedStr {
    fn cmp(&self, other: &InternedStr) -> Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl Hash for InternedStr {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: Hasher,
    {
        self.as_ptr().hash(hasher)
    }
}

unsafe impl Sync for InternedStr {}

impl Deref for InternedStr {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for InternedStr {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl InternedStr {
    pub fn inner(&self) -> GcStr {
        self.0
    }
}

#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct Interner {
    // Interned strings that are referenced will be inserted anyway so we can skip serializing this
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    // For this map and this map only we can't use InternedStr as keys since the hash should
    // not be expected to be the same as ordinary strings, we use a transmute to &'static str to
    // have the keys as strings without any unsafety as the keys do not escape the interner and they
    // live as long as their values
    indexes: FnvMap<&'static str, InternedStr>,
}

impl Traverseable for Interner {
    fn traverse(&self, gc: &mut Gc) {
        for (_, v) in self.indexes.iter() {
            v.0.traverse(gc);
        }
    }
}

impl Interner {
    pub fn new() -> Interner {
        Interner {
            indexes: FnvMap::default(),
        }
    }

    pub fn intern(&mut self, gc: &mut Gc, s: &str) -> Result<InternedStr> {
        match self.indexes.get(s) {
            Some(interned_str) => return Ok(*interned_str),
            None => (),
        }
        let gc_str = unsafe { InternedStr(GcStr::from_utf8_unchecked(gc.alloc(s.as_bytes())?)) };
        // The key will live as long as the value it refers to and the static str never escapes
        // outside interner so this is safe
        let key: &'static str = unsafe { ::std::mem::transmute::<&str, &'static str>(&gc_str) };
        self.indexes.insert(key, gc_str);
        Ok(gc_str)
    }
}

impl fmt::Debug for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InternedStr({:p}, {:?})", &*self.0, self.0)
    }
}
impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self[..])
    }
}
