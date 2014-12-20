use std::collections::HashMap;
use std::fmt;
use std::mem;

use gc::{GcPtr, Gc, DataDef};

pub type InternedStr = GcPtr<str>;


pub struct Interner {
    indexes: HashMap<GcPtr<str>, GcPtr<str>>
}

struct StrDef<'a>(&'a str);

impl <'a> DataDef<str> for StrDef<'a> {
    fn size(&self) -> uint {
        self.0.len()
    }
    fn initialize(&self, ptr: *mut str) {
        let ptr: &mut [u8] = unsafe { mem::transmute::<&[u8], &mut [u8]>((&*ptr).as_bytes()) };
        assert_eq!(self.0.len(), ptr.len());
        ::std::slice::bytes::copy_memory(ptr, self.0.as_bytes());
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut str {
        unsafe {
            use std::raw::Slice;
            let bytes = mem::transmute::<*mut (), *mut u8>(ptr);
            let x = Slice { data: &*bytes, len: self.0.len() };
            let x: &[u8] = mem::transmute(x);
            mem::transmute(::std::str::from_utf8_unchecked(x))
        }
    }
}

impl Interner {

    pub fn new() -> Interner {
        Interner { indexes: HashMap::new() }
    }

    pub fn intern(&mut self, gc: &mut Gc, s: &str) -> GcPtr<str> {
        match self.indexes.get(s) {
            Some(interned_str) => {
                return *interned_str
            }
            None => ()
        }
        let gc_str: GcPtr<str> = gc.alloc(StrDef(s));
        self.indexes.insert(gc_str, gc_str);
        gc_str
    }
}

impl Str for InternedStr {
    fn as_slice<'a>(&'a self) -> &'a str {
        &**self
    }
}

impl fmt::Show for InternedStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_slice())
    }
}

#[cfg(test)]
pub mod tests {
    use std::rc::Rc;
    use std::cell::RefCell;
    use super::*;
    use gc::Gc;

///Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<(Interner, Gc)>> {
    thread_local!(static INTERNER: Rc<RefCell<(Interner, Gc)>> = Rc::new(RefCell::new((Interner::new(), Gc::new()))))
    INTERNER.with(|interner| interner.clone())
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    let mut i = i.borrow_mut();
    let &(ref mut i, ref mut gc) = &mut *i;
    i.intern(gc, s)
}

}
