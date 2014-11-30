use std::cell::{RefCell, Ref};
use std::collections::HashMap;
use std::hash::Hash;
use std::mem::transmute;

//A mapping between K and V where once a value has been inserted it cannot be changed
//Through this and the fact the all values are stored as pointers it is possible to safely
//insert new values without invalidating pointers retrieved from it
pub struct FixedMap<K, V> {
    map: RefCell<HashMap<K, Box<V>>>
}
impl <K: Eq + Hash, V> FixedMap<K, V> {

    pub fn new() -> FixedMap<K, V> {
        FixedMap { map: RefCell::new(HashMap::new()) }
    }

    pub fn try_insert(&self, key: K, value: V) -> Result<(), (K, V)> {
        if self.get(&key).is_some() {
            Err((key, value))
        }
        else {
            self.map.borrow_mut().insert(key, box value);
            Ok(())
        }
    }

    pub fn len(&self) -> uint {
        self.map.borrow().len()
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        self.map.borrow()
            .get(k)
            .map(|x| unsafe { transmute::<&V, &V>(&**x) })
    }

}

pub struct FixedVec<T> {
    vec: RefCell<Vec<Box<T>>>
}

impl <T> FixedVec<T> {
    pub fn new() -> FixedVec<T> {
        FixedVec { vec: RefCell::new(Vec::new()) }
    }

    pub fn push(&self, value: T) {
        self.vec.borrow_mut().push(box value)
    }
    pub fn extend<I: Iterator<T>>(&self, iter: I) {
        self.vec.borrow_mut().extend(iter.map(|v| box v))
    }

    pub fn borrow(&self) -> Ref<Vec<Box<T>>> {
        self.vec.borrow()
    }

    pub fn find(&self, test: |&T| -> bool) -> Option<(uint, &T)> {
        self.vec.try_borrow()
            .and_then(|vec| {
                vec.iter()
                    .enumerate()
                    .find(|&(_, boxed)| test(&**boxed))
                    .map(|(i, boxed)| (i, unsafe { transmute::<&T, &T>(&**boxed) }))
            })
    }

    pub fn len(&self) -> uint {
        self.vec.borrow().len()
    }
}

impl <T> Index<uint, T> for FixedVec<T> {
    fn index(&self, index: &uint) -> &T {
        let vec = self.vec.borrow();
        let result = &*(*vec)[*index];
        unsafe { transmute::<&T, &T>(result) }
    }
}


impl <A> FromIterator<A> for FixedVec<A> {
    fn from_iter<T: Iterator<A>>(iterator: T) -> FixedVec<A> {
        let vec: Vec<_> = iterator.map(|x| box x).collect();
        FixedVec { vec: RefCell::new(vec) }
    }
}
