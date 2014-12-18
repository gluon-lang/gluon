use std::collections::HashMap;
use std::fmt;

#[deriving(Eq, PartialEq, Clone, Default, Hash)]
pub struct InternedStr(&'static str);

impl Copy for InternedStr { }

#[deriving(Clone)]
pub struct Interner {
    indexes: HashMap<&'static str, String>
}

impl Interner {

    pub fn new() -> Interner {
        Interner { indexes: HashMap::new() }
    }

    pub fn intern(&mut self, s: &str) -> InternedStr {
        match self.indexes.get(s) {
            Some(interned_str) => {
                let index: &'static str = unsafe { ::std::mem::transmute(interned_str.as_slice()) };
                return InternedStr(index);
            }
            None => ()
        }
        let val = s.to_string();
        let index: &'static str = unsafe { ::std::mem::transmute(val.as_slice()) };
        self.indexes.insert(index, val);
        InternedStr(index)
    }
}

impl Str for InternedStr {
    fn as_slice<'a>(&'a self) -> &'a str {
        let InternedStr(s) = *self;
        s
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

///Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<Interner>> {
    thread_local!(static INTERNER: Rc<RefCell<Interner>> = Rc::new(RefCell::new(Interner::new())))
    INTERNER.with(|interner| interner.clone())
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    (*i).borrow_mut().intern(s)
}

}
