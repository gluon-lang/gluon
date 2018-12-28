//! Collection types which allows insertion of new values while shared references to its contents
//! are alive. This is done by storing each value in a stable memory location and preventing an
//! earlier inserted value to be overwritten.
use std::borrow::Borrow;
use std::cell::RefCell;
use std::fmt;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::ops::{DerefMut, Index, IndexMut};

use stable_deref_trait::StableDeref;

use crate::fnv::FnvMap;
// NOTE: transmute is used to circumvent the borrow checker in this module
// This is safe since the containers hold boxed values meaning allocating larger
// storage does not invalidate the references that are handed out and because values
// can only be inserted, never modified (this could be done with a Rc pointer as well but
// is not done for efficiency since it is not needed)

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

unsafe fn forget_lifetime_mut<'a, 'b, T: ?Sized>(x: &'a mut T) -> &'b mut T {
    ::std::mem::transmute(x)
}

// A mapping between K and V where once a value has been inserted it cannot be changed
// Through this and the fact the all values are stored as pointers it is possible to safely
// insert new values without invalidating pointers retrieved from it
pub struct FixedMap<K, V> {
    map: RefCell<FnvMap<K, V>>,
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

impl<K: Eq + Hash, V: StableDeref> FixedMap<K, V> {
    pub fn try_insert(&self, key: K, value: V) -> Result<(), (K, V)> {
        if self.get(&key).is_some() {
            Err((key, value))
        } else {
            self.map.borrow_mut().insert(key, value);
            Ok(())
        }
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V::Target>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map
            .borrow()
            .get(k)
            .map(|x| unsafe { forget_lifetime(&**x) })
    }
}

impl<'a, Q, K, V> Index<&'a Q> for FixedMap<K, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    V: StableDeref,
{
    type Output = V::Target;
    fn index(&self, index: &'a Q) -> &Self::Output {
        let map = self.map.borrow();
        let result = &*map[index];
        unsafe { forget_lifetime(result) }
    }
}

#[derive(Debug)]
pub struct FixedVec<T> {
    vec: RefCell<Vec<T>>,
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
        }
    }

    pub fn clear(&mut self) {
        self.vec.borrow_mut().clear();
    }

    pub fn push(&self, value: T) {
        self.vec.borrow_mut().push(value)
    }

    #[allow(dead_code)]
    pub fn extend<I: IntoIterator<Item = T>>(&self, iter: I) {
        self.vec.borrow_mut().extend(iter)
    }

    pub fn len(&self) -> usize {
        self.vec.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> FixedVec<T>
where
    T: StableDeref,
{
    pub fn iter(&self) -> impl Iterator<Item = &T::Target> {
        (0..).scan((), move |_, i| self.get(i))
    }

    pub fn get(&self, index: usize) -> Option<&T::Target> {
        if index < self.len() {
            Some(&self[index])
        } else {
            None
        }
    }
}

impl<T> Index<usize> for FixedVec<T>
where
    T: StableDeref,
{
    type Output = T::Target;
    fn index(&self, index: usize) -> &T::Target {
        let vec = self.vec.borrow();
        let result = &*vec[index];
        unsafe { forget_lifetime(result) }
    }
}

impl<T> IndexMut<usize> for FixedVec<T>
where
    T: StableDeref + DerefMut,
{
    fn index_mut(&mut self, index: usize) -> &mut T::Target {
        let mut vec = self.vec.borrow_mut();
        let result = &mut *vec[index];
        unsafe { forget_lifetime_mut(result) }
    }
}

impl<A> FromIterator<A> for FixedVec<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iterator: T) -> FixedVec<A> {
        let vec: Vec<_> = iterator.into_iter().collect();
        FixedVec {
            vec: RefCell::new(vec),
        }
    }
}
