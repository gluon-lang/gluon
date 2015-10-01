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

pub trait Variable {
    fn get_id(&self) -> u32;
}

impl Variable for u32 {
    fn get_id(&self) -> u32 {
        *self
    }
}

pub trait Substitutable: PartialEq + Clone {
    type Variable: Variable;
    fn new(x: u32) -> Self;
    fn from_variable(x: Self::Variable) -> Self;
    fn get_var(&self) -> Option<&Self::Variable>;
    fn occurs(&self, subs: &Substitution<Self>, var: &Self::Variable) -> bool;
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
            Some(var) => match self.find_type_for_var(var.get_id()) {
                Some(t) => t,
                None => typ
            },
            _ => typ
        }
    }

    pub fn make_real(&self, typ: &mut T) {
        *typ = match typ.get_var() {
            Some(var) => match self.find_type_for_var(var.get_id()) {
                Some(t) => t.clone(),
                None => return
            },
            None => return
        };
    }

    pub fn find_type_for_var(&self, var: u32) -> Option<&T> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let map = unsafe { &mut *self.map.get() };
        map.get_mut(&var).map(|typ| {
            let new_type = match typ.get_var() {
                Some(parent_var) if parent_var.get_id() != var => {
                    match self.find_type_for_var(parent_var.get_id()) {
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
            var = v.get_var().map(|v| v.get_id()).unwrap_or(var);
        }
        let map = unsafe { &mut *self.levels.get() };
        map.get(&var).cloned().unwrap_or(var)
    }

    pub fn union(&self, id: &T::Variable, typ: &T) -> Result<(), ()>
    where T::Variable: Clone {
        if typ.occurs(self, id) {
            return Err(())
        }
        {
            let id_type = self.find_type_for_var(id.get_id());
            let other_type = self.real(typ);
            if id_type.map(|x| x == other_type).unwrap_or(other_type.get_var().map(|y| y.get_id()) == Some(id.get_id())) {
                return Ok(())
            }
        }
        let map: &mut _ = unsafe { &mut *self.map.get() };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match typ.get_var() {
            Some(other_id) if self.get_level(id.get_id()) < self.get_level(other_id.get_id()) => {
                map.insert(other_id.get_id(), Box::new(T::from_variable(id.clone())));
                self.update_level(id.get_id(), other_id.get_id());
            }
            _ => {
                map.insert(id.get_id(), Box::new(typ.clone()));
            }
        };
        Ok(())
    }
}
