//! A map data type which allows the same key to exist at multiple scope levels
use std::borrow::Borrow;
use std::collections::hash_map;
use std::collections::hash_map::{Entry, IterMut};
use std::hash::Hash;

use fnv::FnvMap;

/// A map struct which allows for the introduction of different scopes
/// Introducing a new scope will make it possible to introduce additional
/// variables with names already defined, shadowing the old name
/// After exiting a scope the shadowed variable will again be re introduced
#[derive(Debug)]
pub struct ScopedMap<K: Eq + Hash + Clone, V> {
    /// A hashmap storing a key -> value mapping
    /// Stores a vector of values in which the value at the top is value returned from 'get'
    map: FnvMap<K, Vec<V>>,
    /// A vector of scopes, when entering a scope, None is added as a marker
    /// when later exiting a scope, values are removed from the map until the marker is found
    scopes: Vec<Option<K>>,
}

#[allow(dead_code)]
impl<K: Eq + Hash + Clone, V> ScopedMap<K, V> {
    pub fn new() -> ScopedMap<K, V> {
        ScopedMap {
            map: FnvMap::default(),
            scopes: Vec::new(),
        }
    }

    /// Introduces a new scope
    pub fn enter_scope(&mut self) {
        self.scopes.push(None);
    }

    /// Exits the current scope, returning an iterator over the (key, value) pairs that are removed
    /// When `ExitScopeIter` is dropped any remaining pairs of the scope is removed as well.
    pub fn exit_scope(&mut self) -> ExitScopeIter<K, V> {
        ExitScopeIter {
            map: self,
            done: false,
        }
    }

    /// Removes a previusly inserted value from the map.
    pub fn remove(&mut self, k: &K) -> bool {
        match self.map.get_mut(k).map(|x| x.pop()) {
            Some(..) => {
                let mut i = self.scopes.len() as isize - 1;
                while i >= 0 {
                    if self.scopes[i as usize].as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as usize);
                    }
                    i -= 1;
                }
                true
            }
            None => false,
        }
    }

    /// Returns true if the key has a value declared in the last declared scope
    pub fn in_current_scope(&self, k: &K) -> bool {
        for n in self.scopes.iter().rev() {
            match *n {
                Some(ref name) if name == k => return true,
                None => break,
                _ => (),
            }
        }
        false
    }

    /// Returns an iterator of the (key, values) pairs inserted in the map
    pub fn iter_mut(&mut self) -> IterMut<K, Vec<V>> {
        self.map.iter_mut()
    }

    /// Returns a reference to the last inserted value corresponding to the key
    pub fn get<'a, Q: ?Sized>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map.get(k).and_then(|x| x.last())
    }

    /// Returns a reference to the all inserted value corresponding to the key
    pub fn get_all<'a, Q: ?Sized>(&'a self, k: &Q) -> Option<&'a [V]>
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.map.get(k).map(|x| &x[..])
    }

    /// Returns the number of elements in the container.
    /// Shadowed elements are not counted
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if this map is empty
    pub fn is_empty(&self) -> bool {
        self.map.len() == 0
    }

    /// Removes all elements
    pub fn clear(&mut self) {
        self.map.clear();
        self.scopes.clear();
    }

    /// Swaps the value stored at key, or inserts it if it is not present
    pub fn swap(&mut self, k: K, v: V) -> Option<V> {
        let vec = match self.map.entry(k.clone()) {
            Entry::Occupied(v) => v.into_mut(),
            Entry::Vacant(v) => v.insert(Vec::new()),
        };
        if vec.is_empty() {
            vec.push(v);
            self.scopes.push(Some(k));
            None
        } else {
            let r = vec.pop();
            vec.push(v);
            r
        }
    }

    pub fn pop(&mut self, k: &K) -> Option<V> {
        match self.map.get_mut(k).and_then(|x| x.pop()) {
            Some(v) => {
                let mut i = self.scopes.len() as isize - 1;
                while i >= 0 {
                    if self.scopes[i as usize].as_ref().map_or(false, |x| x == k) {
                        self.scopes.remove(i as usize);
                    }
                    i -= 1;
                }
                Some(v)
            }
            None => None,
        }
    }

    pub fn get_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        self.map.get_mut(key).and_then(|x| {
            let last = x.len() - 1;
            x.get_mut(last)
        })
    }

    pub fn insert(&mut self, k: K, v: V) -> bool {
        let vec = match self.map.entry(k.clone()) {
            Entry::Occupied(v) => v.into_mut(),
            Entry::Vacant(v) => v.insert(Vec::new()),
        };
        vec.push(v);
        self.scopes.push(Some(k));
        vec.len() == 1
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.map.iter(),
        }
    }
}

impl<K: Eq + Hash + Clone, V> Extend<(K, V)> for ScopedMap<K, V> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = (K, V)>,
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

pub struct Iter<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    iter: hash_map::Iter<'a, K, Vec<V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            match self.iter.next() {
                Some((k, vs)) => if let Some(v) = vs.last() {
                    return Some((k, v));
                },
                None => return None,
            }
        }
    }
}

pub struct ExitScopeIter<'a, K, V>
where
    K: 'a + Eq + Hash + Clone,
    V: 'a,
{
    map: &'a mut ScopedMap<K, V>,
    done: bool,
}

impl<'a, K, V> Drop for ExitScopeIter<'a, K, V>
where
    K: Eq + Hash + Clone,
{
    fn drop(&mut self) {
        for _ in self {}
    }
}

impl<'a, K, V> Iterator for ExitScopeIter<'a, K, V>
where
    K: Eq + Hash + Clone,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            None
        } else {
            match self.map.scopes.pop() {
                Some(Some(key)) => {
                    let result = self.map.map.get_mut(&key).and_then(|x| x.pop());
                    self.done = result.is_none();
                    result.map(|value| (key, value))
                }
                _ => {
                    self.done = true;
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use scoped_map::ScopedMap;
    #[test]
    fn test() {
        let mut map = ScopedMap::new();
        map.insert("a", 0);
        map.insert("b", 1);
        map.enter_scope();
        assert_eq!(map.get(&"a"), Some(&0));
        assert_eq!(map.get(&"b"), Some(&1));
        assert_eq!(map.get(&"c"), None);
        map.insert("a", 1);
        map.insert("c", 2);
        assert_eq!(map.get(&"a"), Some(&1));
        assert_eq!(map.get(&"c"), Some(&2));
        map.exit_scope();
        assert_eq!(map.get(&"a"), Some(&0));
        assert_eq!(map.get(&"c"), None);
    }
}
