use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use base::ast::{AstId, DisplayEnv, IdentEnv, AstType};
use base::types::FnvMap;

use gc::{GcPtr, Gc, Traverseable};
use array::Str;

/// Interned strings which allow for fast equality checks and hashing
#[derive(Copy, Clone, Eq)]
pub struct InternedStr(GcPtr<Str>);

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

impl Hash for InternedStr {
    fn hash<H>(&self, hasher: &mut H)
        where H: Hasher
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
    pub fn inner(&self) -> GcPtr<Str> {
        self.0
    }
}

pub struct Interner {
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
        Interner { indexes: FnvMap::default() }
    }

    pub fn intern(&mut self, gc: &mut Gc, s: &str) -> InternedStr {
        match self.indexes.get(s) {
            Some(interned_str) => return *interned_str,
            None => (),
        }
        let gc_str = InternedStr(gc.alloc(s));
        // The key will live as long as the value it refers to and the static str never escapes
        // outside interner so this is safe
        let key: &'static str = unsafe { ::std::mem::transmute::<&str, &'static str>(&gc_str) };
        self.indexes.insert(key, gc_str);
        gc_str
    }
}

impl fmt::Debug for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InternedStr({:?})", self.0)
    }
}
impl fmt::Display for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self[..])
    }
}

pub struct InternerEnv<'a>(&'a mut Interner, &'a mut Gc);

impl<'a> InternerEnv<'a> {
    pub fn intern(&mut self, s: &str) -> InternedStr {
        self.0.intern(self.1, s)
    }
}

impl<'i> DisplayEnv for InternerEnv<'i> {
    type Ident = InternedStr;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.0
            .indexes
            .get(&**ident)
            .map(|x| &**x)
            .unwrap_or("<UNKNOWN>")
    }
}
impl<'a> IdentEnv for InternerEnv<'a> {
    fn from_str(&mut self, s: &str) -> InternedStr {
        self.intern(s)
    }
}

impl AstId for InternedStr {
    type Untyped = InternedStr;

    fn to_id(self) -> InternedStr {
        self
    }
    fn set_type(&mut self, _: AstType<Self::Untyped>) {}
}
