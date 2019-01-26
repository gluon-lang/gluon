//! Collection types which allows insertion of new values while shared references to its contents
//! are alive. This is done by storing each value in a stable memory location and preventing an
//! earlier inserted value to be overwritten.
use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::hash_map::Entry,
    fmt,
    hash::Hash,
    iter::IntoIterator,
    mem,
    ops::{Index, IndexMut},
};

use crate::fnv::FnvMap;
// NOTE: transmute is used to circumvent the borrow checker in this module
// This is safe since the containers hold boxed values meaning allocating larger
// storage does not invalidate the references that are handed out and because values
// can only be inserted, never modified (this could be done with a Rc pointer as well but
// is not done for efficiency since it is not needed)

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

// A mapping between K and V where once a value has been inserted it cannot be changed
// Through this and the fact the all values are stored as pointers it is possible to safely
// insert new values without invalidating pointers retrieved from it
pub struct FixedMap<K, V> {
    map: RefCell<FnvMap<K, (u32, u32)>>,
    values: Buffer<V>,
}

impl<K: Eq + Hash, V> Default for FixedMap<K, V> {
    fn default() -> FixedMap<K, V> {
        FixedMap::new()
    }
}

impl<K: Eq + Hash + fmt::Debug, V: fmt::Debug> fmt::Debug for FixedMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.map.borrow().fmt(f)
    }
}

impl<K: Eq + Hash, V> FixedMap<K, V> {
    pub fn new() -> FixedMap<K, V> {
        FixedMap {
            map: RefCell::new(FnvMap::default()),
            values: Default::default(),
        }
    }

    pub fn clear(&mut self) {
        self.map.borrow_mut().clear();
    }

    pub fn len(&self) -> usize {
        self.map.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K: Eq + Hash, V> FixedMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.map.get_mut().entry(key) {
            Entry::Occupied(entry) => Some(mem::replace(&mut self.values[*entry.get()], value)),
            Entry::Vacant(entry) => {
                entry.insert(self.values.push(value));
                None
            }
        }
    }

    pub fn try_insert(&self, key: K, value: V) -> Result<(), (K, V)> {
        if self.get(&key).is_some() {
            Err((key, value))
        } else {
            let index_value = self.values.push(value);
            self.map.borrow_mut().insert(key, index_value);
            Ok(())
        }
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq + Hash,
    {
        self.map.borrow().get(k).map(|key| &self.values[*key])
    }

    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        let values = &mut self.values;
        self.map.get_mut().get(k).map(move |&key| &mut values[key])
    }
}

impl<'a, Q, K, V> Index<&'a Q> for FixedMap<K, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
{
    type Output = V;
    fn index(&self, index: &'a Q) -> &Self::Output {
        self.get(index).expect("Index out of bounds")
    }
}

#[derive(Debug)]
pub struct FixedVec<T> {
    vec: RefCell<Vec<(u32, u32)>>,
    values: Buffer<T>,
}

impl<T> Default for FixedVec<T> {
    fn default() -> Self {
        FixedVec::new()
    }
}

impl<T> FixedVec<T> {
    pub fn new() -> FixedVec<T> {
        FixedVec {
            vec: RefCell::new(Vec::new()),
            values: Default::default(),
        }
    }

    pub fn clear(&mut self) {
        self.vec.borrow_mut().clear();
    }

    pub fn push(&self, value: T) {
        let key = self.values.push(value);
        self.vec.borrow_mut().push(key);
    }

    pub fn extend<I: IntoIterator<Item = T>>(&self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }

    pub fn len(&self) -> usize {
        self.vec.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> FixedVec<T> {
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        (0..).scan((), move |_, i| self.get(i))
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            Some(&self[index])
        } else {
            None
        }
    }
}

impl<T> Index<usize> for FixedVec<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        let vec = self.vec.borrow();
        &self.values[vec[index]]
    }
}

impl<T> IndexMut<usize> for FixedVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        let vec = self.vec.borrow();
        &mut self.values[vec[index]]
    }
}

#[derive(Debug)]
struct Buffer<T> {
    values: RefCell<Vec<Vec<T>>>,
}

impl<T> Default for Buffer<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Buffer<T> {
    pub fn new() -> Self {
        Self {
            values: Default::default(),
        }
    }

    fn push(&self, value: T) -> (u32, u32) {
        let mut values = self.values.borrow_mut();
        let cap = match values.last() {
            Some(vec) => {
                if vec.len() == vec.capacity() {
                    Some(vec.capacity() * 2)
                } else {
                    None
                }
            }
            None => Some(4),
        };
        if let Some(cap) = cap {
            values.push(Vec::with_capacity(cap));
        }

        let i = values.len() as u32 - 1;
        let inner = values.last_mut().unwrap();
        let j = inner.len() as u32;
        inner.push(value);
        (i, j)
    }
}

impl<T> Index<(u32, u32)> for Buffer<T> {
    type Output = T;
    fn index(&self, (i, j): (u32, u32)) -> &T {
        unsafe { forget_lifetime(&self.values.borrow()[i as usize][j as usize]) }
    }
}

impl<T> IndexMut<(u32, u32)> for Buffer<T> {
    fn index_mut(&mut self, (i, j): (u32, u32)) -> &mut T {
        &mut self.values.get_mut()[i as usize][j as usize]
    }
}
