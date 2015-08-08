use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use base::interner::InternedStr;

pub struct Substitution<T> {
    pub map: UnsafeCell<HashMap<u32, Box<T>>>,
    levels: UnsafeCell<HashMap<u32, u32>>,
    pub variables: RefCell<HashMap<InternedStr, T>>,
    pub var_id: Cell<u32>
}

pub trait Substitutable: Clone {
    fn new(x: u32) -> Self;
    fn get_var(&self) -> Option<u32>;
}

impl <T: fmt::Debug> fmt::Debug for Substitution<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let map: &_ = unsafe { &*self.map.get() };
        write!(f, "Substitution {{ map: {:?}, variables: {:?}, var_id: {:?} }}",
               map, self.variables.borrow(), self.var_id.get())
    }
}

impl <T: Substitutable> Substitution<T> {
    pub fn new() -> Substitution<T> {
        Substitution {
            map: UnsafeCell::new(HashMap::new()),
            levels: UnsafeCell::new(HashMap::new()),
            variables: RefCell::new(HashMap::new()),
            var_id: Cell::new(1)
        }
    }

    pub fn clear(&mut self) {
        unsafe { (*self.map.get()).clear(); }
        self.variables.borrow_mut().clear();
        self.var_id.set(1);
    }

    pub unsafe fn insert(&mut self, var: u32, t: T) {
        (*self.map.get()).insert(var, Box::new(t));
    }

    pub fn new_var(&mut self) -> T {
        self.var_id.set(self.var_id.get() + 1);
        T::new(self.var_id.get())
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

    pub fn variable_for(&self, id: InternedStr) -> T {
        let mut variables = self.variables.borrow_mut();
        match variables.entry(id) {
            Entry::Vacant(entry) => {
                self.var_id.set(self.var_id.get() + 1);
                entry.insert(T::new(self.var_id.get())).clone()
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
