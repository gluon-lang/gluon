use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use base::interner::InternedStr;

pub struct Substitution<T> {
    pub map: UnsafeCell<HashMap<u32, Box<T>>>,
    levels: UnsafeCell<HashMap<u32, u32>>,
    pub variables: HashMap<InternedStr, T>,
    pub var_id: u32
}

pub trait Substitutable: Clone {
    fn new(x: u32) -> Self;
    fn get_var(&self) -> Option<u32>;
}

impl <T: fmt::Debug> fmt::Debug for Substitution<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let map: &_ = unsafe { &*self.map.get() };
        write!(f, "Substitution {{ map: {:?}, variables: {:?}, var_id: {:?} }}",
               map, self.variables, self.var_id)
    }
}

impl <T: Substitutable> Substitution<T> {
    pub fn new() -> Substitution<T> {
        Substitution {
            map: UnsafeCell::new(HashMap::new()),
            levels: UnsafeCell::new(HashMap::new()),
            variables: HashMap::new(),
            var_id: 1
        }
    }

    pub fn clear(&mut self) {
        unsafe { (*self.map.get()).clear(); }
        self.variables.clear();
        self.var_id = 1;
    }

    pub unsafe fn insert(&mut self, var: u32, t: T) {
        (*self.map.get()).insert(var, Box::new(t));
    }

    pub fn new_var(&mut self) -> T {
        self.var_id += 1;
        T::new(self.var_id)
    }

    pub fn real<'r>(&'r self, typ: &'r T) -> &'r T {
        match typ.get_var() {
            Some(var) => match self.find_type_for_var(var) {
                Some(t) => t,
                None => typ
            },
            _ => typ
        }
    }

    pub fn find_type_for_var(&self, var: u32) -> Option<&T> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let map = unsafe { &mut *self.map.get() };
        map.get_mut(&var).map(|typ| {
            let new_type = match typ.get_var() {
                Some(parent_var) if parent_var != var => {
                    match self.find_type_for_var(parent_var) {
                        Some(other) => Some(other.clone()),
                        None => None
                    }
                }
                _ => None
            };
            if let Some(new_type) = new_type {
                **typ = new_type;
            }
            &**typ
        })
    }

    pub fn variable_for(&mut self, id: InternedStr) -> T {
        match self.variables.entry(id) {
            Entry::Vacant(entry) => {
                self.var_id += 1;
                entry.insert(T::new(self.var_id)).clone()
            }
            Entry::Occupied(entry) => entry.get().clone()
        }
    }

    pub fn update_level(&self, var: u32, other: u32) {
        let map = unsafe { &mut *self.levels.get() };
        let level = self.get_level(var);
        match map.get_mut(&other) {
            Some(t) => {
                *t = ::std::cmp::min(*t, level);
                return
            }
            None => ()
        }
        map.insert(other, ::std::cmp::min(other, level));
    }
    pub fn get_level(&self, mut var: u32) -> u32 {
        if let Some(v) = self.find_type_for_var(var) {
            var = v.get_var().unwrap_or(var);
        }
        let map = unsafe { &mut *self.levels.get() };
        map.get(&var).cloned().unwrap_or(var)
    }
}
