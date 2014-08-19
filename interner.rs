use std::collections::HashMap;
use std::fmt;

#[deriving(Eq, PartialEq, Clone, Default, Hash)]
pub struct InternedStr(&'static str);

#[deriving(Clone)]
pub struct Interner {
    indexes: HashMap<&'static str, String>
}

impl Interner {

    pub fn new() -> Interner {
        Interner { indexes: HashMap::new() }
    }

    pub fn intern(&mut self, s: &str) -> InternedStr {
        match self.indexes.find_equiv(&s) {
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
    local_data_key!(key: Rc<RefCell<Interner>>)
    match key.get() {
        Some(interner) => interner.clone(),
        None => {
            let interner = Rc::new(RefCell::new(Interner::new()));
            key.replace(Some(interner.clone()));
            interner
        }
    }
}

pub fn intern(s: &str) -> InternedStr {
    let i = get_local_interner();
    (*i).borrow_mut().intern(s)
}

}
