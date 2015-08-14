use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::Deref;
use ast::{AstId, IdentEnv, ASTType};

use gc::{GcPtr, Gc, DataDef, Traverseable};

/// Interned strings which allow for fast equality checks and hashing
#[derive(Copy, Clone, Eq)]
pub struct InternedStr(GcPtr<str>);

impl PartialEq<InternedStr> for InternedStr {
    fn eq(&self, other: &InternedStr) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}
impl <'a> PartialEq<&'a str> for InternedStr {
    fn eq(&self, other: & &'a str) -> bool {
        **self == **other
    }
}

impl Hash for InternedStr {
    fn hash<H>(&self, hasher: &mut H) where H: Hasher {
        self.as_ptr().hash(hasher)
    }
}

unsafe impl Sync for InternedStr { }

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
    pub fn inner(&self) -> GcPtr<str> {
        self.0
    }
}

pub struct Interner {
    //For this map and this map only we can't use InternedStr as keys since the hash should
    //not be expected to be the same as ordinary strings, we use a transmute to &'static str to
    //have the keys as strings without any unsafety as the keys do not escape the interner and they
    //live as long as their values
    indexes: HashMap<&'static str, InternedStr>
}

unsafe impl <'a> DataDef for &'a str {
    type Value = str;
    fn size(&self) -> usize {
        self.len()
    }
    fn initialize(self, ptr: *mut str) {
        let ptr: &mut [u8] = unsafe { mem::transmute::<*mut str, &mut [u8]>(ptr) };
        assert_eq!(self.len(), ptr.len());
        ::std::slice::bytes::copy_memory(self.as_bytes(), ptr);
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut str {
        unsafe {
            use std::raw::Slice;
            let x = Slice { data: ptr as *mut u8, len: self.len() };
            mem::transmute(x)
        }
    }
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
        Interner { indexes: HashMap::new() }
    }

    pub fn intern(&mut self, gc: &mut Gc, s: &str) -> InternedStr {
        match self.indexes.get(s) {
            Some(interned_str) => {
                return *interned_str
            }
            None => ()
        }
        let gc_str = InternedStr(gc.alloc(s));
        //The key will live as long as the value it refers to and the static str never escapes
        //outside interner so this is safe
        let key: &'static str = unsafe { ::std::mem::transmute::<&str, &'static str>(&gc_str) };
        self.indexes.insert(key, gc_str);
        gc_str
    }

    pub fn with_env<'a, F, R>(&'a mut self, gc: &'a mut Gc, f: F) -> R
        where F: FnOnce(InternerEnv<'a>) -> R {
        f(InternerEnv(self, gc))
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

impl <'a> InternerEnv<'a> {
    pub fn intern(&mut self, s: &str) -> InternedStr {
        self.0.intern(self.1, s)
    }
}

impl <'a> IdentEnv for InternerEnv<'a> {
    type Ident = InternedStr;

    fn from_str(&mut self, s: &str) -> InternedStr {
        self.intern(s)
    }
}

impl AstId for InternedStr {
    type Untyped = InternedStr;

    fn to_id(self) -> InternedStr { self }
    fn set_type(&mut self, _: ASTType<Self::Untyped>) { }
}

#[cfg(test)]
pub mod tests {
    use std::rc::Rc;
    use std::cell::RefCell;
    use super::*;
    use gc::Gc;

///Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<(Interner, Gc)>> {
    thread_local!(static INTERNER: Rc<RefCell<(Interner, Gc)>> = Rc::new(RefCell::new((Interner::new(), Gc::new()))));
    INTERNER.with(|interner| interner.clone())
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    let mut i = i.borrow_mut();
    let &mut(ref mut i, ref mut gc) = &mut *i;
    i.intern(gc, s)
}

}
