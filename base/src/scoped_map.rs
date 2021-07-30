//! A map data type which allows the same key to exist at multiple scope levels
use std::borrow::Borrow;
use std::collections::hash_map::{self, IterMut};
use std::fmt;
use std::hash::Hash;

use crate::fnv::FnvMap;

/// A map struct which allows for the introduction of different scopes
/// Introducing a new scope will make it possible to introduce additional
/// variables with names already defined, shadowing the old name
/// After exiting a scope the shadowed variable will again be re introduced
pub struct ScopedMap<K: Eq + Hash, V> {
    /// A hashmap storing a key -> value mapping
    /// Stores a vector of values in which the value at the top is value returned from 'get'
    map: FnvMap<K, Vec<V>>,
    /// A vector of scopes, when entering a scope, None is added as a marker
    /// when later exiting a scope, values are removed from the map until the marker is found
    scopes: Vec<Option<K>>,
}

impl<K: Eq + Hash, V> Default for ScopedMap<K, V> {
    fn default() -> Self {
        ScopedMap {
            map: FnvMap::default(),
            scopes: Vec::default(),
        }
    }
}

impl<K, V> fmt::Debug for ScopedMap<K, V>
where
    K: Eq + Hash + fmt::Debug + Clone,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[allow(dead_code)]
impl<K: Eq + Hash + Clone, V> ScopedMap<K, V> {
    pub fn new() -> ScopedMap<K, V> {
        ScopedMap::default()
    }

    pub fn num_scopes(&self) -> usize {
        self.scopes.iter().filter(|s| s.is_none()).count() + 1
    }

    /// Introduces a new scope
    pub fn enter_scope(&mut self) {
        self.scopes.push(None);
    }

    pub fn current_scope(&self) -> impl Iterator<Item = (&K, &V)> {
        self.scopes
            .iter()
            .rev()
            .take_while(|scope| scope.is_some())
            .map(move |scope| {
                let key = scope.as_ref().unwrap();
                let value = self.map.get(key).and_then(|x| x.last()).expect("Value");
                (key, value)
            })
    }

    /// Exits the current scope, returning an iterator over the (key, value) pairs that are removed
    /// When `ExitScopeIter` is dropped any remaining pairs of the scope is removed as well.
    pub fn exit_scope(&mut self) -> ExitScopeIter<K, V> {
        ExitScopeIter {
            map: self,
            done: false,
        }
    }

    /// Removes a previously inserted value from the map.
    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq + Hash,
        K: ::std::fmt::Debug,
        V: ::std::fmt::Debug,
    {
        let x = self.map.get_mut(k).map(|x| x.pop())?;
        let mut i = self.scopes.len() as isize - 1;
        while i >= 0 {
            if self.scopes[i as usize]
                .as_ref()
                .expect("Tried to remove entry not in the current scope")
                .borrow()
                == k
            {
                self.scopes.remove(i as usize);
                break;
            }
            i -= 1;
        }
        x
    }

    /// Returns true if the key has a value declared in the last declared scope
    pub fn in_current_scope<Q>(&self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        for n in self.scopes.iter().rev() {
            match *n {
                Some(ref name) if name.borrow() == k => return true,
                None => break,
                _ => (),
            }
        }
        false
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

    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.map.entry(key) {
            hash_map::Entry::Occupied(entry) => {
                if entry.get().is_empty() {
                    Entry::Vacant(VacantEntry(InnerVacantEntry::Occupied(OccupiedEntry(
                        entry,
                        &mut self.scopes,
                    ))))
                } else {
                    Entry::Occupied(OccupiedEntry(entry, &mut self.scopes))
                }
            }
            hash_map::Entry::Vacant(entry) => Entry::Vacant(VacantEntry(InnerVacantEntry::Vacant(
                entry,
                &mut self.scopes,
            ))),
        }
    }

    pub fn contains_key<'a, Q: ?Sized>(&'a self, k: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash,
    {
        self.get(k).is_some()
    }

    /// Returns the number of elements in the container.
    /// Shadowed elements are counted
    pub fn len(&self) -> usize {
        self.map.values().map(|v| v.len()).sum()
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
        let vec = self.map.entry(k.clone()).or_default();
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
        self.map.get_mut(key).and_then(|x| x.last_mut())
    }

    pub fn insert(&mut self, k: K, v: V) -> bool {
        match self.entry(k) {
            Entry::Occupied(mut entry) => {
                entry.insert(v);
                true
            }
            Entry::Vacant(entry) => {
                entry.insert(v);
                false
            }
        }
    }

    pub fn into_iter(self) -> impl Iterator<Item = (K, V)> {
        self.map
            .into_iter()
            .filter_map(|(k, mut v)| Some((k, v.pop()?)))
    }
}

impl<K: Eq + Hash, V> ScopedMap<K, V> {
    /// Returns an iterator of the (key, values) pairs inserted in the map
    pub fn iter_mut(&mut self) -> IterMut<K, Vec<V>> {
        self.map.iter_mut()
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

pub enum Entry<'a, K, V> {
    Vacant(VacantEntry<'a, K, V>),
    Occupied(OccupiedEntry<'a, K, V>),
}

impl<'a, K, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K: Clone,
    {
        self.or_insert_with(|| default)
    }

    pub fn or_insert_with(self, default: impl FnOnce() -> V) -> &'a mut V
    where
        K: Clone,
    {
        match self {
            Entry::Vacant(entry) => entry.insert(default()),
            Entry::Occupied(entry) => entry.into_mut(),
        }
    }
}

pub enum InnerVacantEntry<'a, K, V> {
    Vacant(hash_map::VacantEntry<'a, K, Vec<V>>, &'a mut Vec<Option<K>>),
    Occupied(OccupiedEntry<'a, K, V>),
}
pub struct VacantEntry<'a, K, V>(InnerVacantEntry<'a, K, V>);
pub struct OccupiedEntry<'a, K, V>(
    hash_map::OccupiedEntry<'a, K, Vec<V>>,
    &'a mut Vec<Option<K>>,
);

impl<'a, K, V> VacantEntry<'a, K, V> {
    pub fn insert(self, value: V) -> &'a mut V
    where
        K: Clone,
    {
        match self.0 {
            InnerVacantEntry::Vacant(entry, scopes) => {
                scopes.push(Some(entry.key().clone()));
                &mut entry.insert(vec![value])[0]
            }
            InnerVacantEntry::Occupied(mut entry) => {
                entry.insert(value);
                entry.into_mut()
            }
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V> {
    pub fn key(&self) -> &K {
        self.0.key()
    }

    pub fn get(&self) -> &V {
        self.0.get().last().unwrap()
    }

    pub fn get_mut(&mut self) -> &mut V {
        self.0.get_mut().last_mut().unwrap()
    }

    pub fn into_mut(self) -> &'a mut V {
        self.0.into_mut().last_mut().unwrap()
    }

    pub fn insert(&mut self, value: V)
    where
        K: Clone,
    {
        self.1.push(Some(self.key().clone()));
        self.0.get_mut().push(value);
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
                Some((k, vs)) => {
                    if let Some(v) = vs.last() {
                        return Some((k, v));
                    }
                }
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
    use super::*;

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

    #[test]
    fn remove() {
        let mut map = ScopedMap::new();
        map.insert("a", 0);
        map.enter_scope();
        map.insert("a", 1);
        map.insert("b", 2);
        assert_eq!(map.get("a"), Some(&1));
        map.remove("a");
        assert_eq!(map.get("a"), Some(&0));
        assert_eq!(map.get("b"), Some(&2));
        map.remove("b");
        assert_eq!(map.get("b"), None);
        map.exit_scope();
    }
}
