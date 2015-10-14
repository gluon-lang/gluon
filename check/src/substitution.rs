use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::default::Default;
use std::fmt;
use union_find::{QuickFindUf, Union, UnionByRank, UnionFind, UnionResult};
use base::fixed::{FixedMap, FixedVec};
use base::interner::InternedStr;

pub struct Substitution<T> {
    map: RefCell<QuickFindUf<UnionByLevel>>,
    variables: FixedVec<T>,
    types: FixedMap<u32, T>,
    pub named_variables: RefCell<HashMap<InternedStr, T>>,
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

#[derive(Debug)]
struct UnionByLevel {
    rank: UnionByRank,
    level: u32
}

impl Default for UnionByLevel {
    fn default() -> UnionByLevel {
        UnionByLevel { rank: UnionByRank::default(), level: ::std::u32::MAX }
    }
}

impl Union for UnionByLevel {
    #[inline]
    fn union(left: UnionByLevel, right: UnionByLevel) -> UnionResult<UnionByLevel> {
        use std::cmp::Ordering;
        let (rank_result, rank) = match Union::union(left.rank, right.rank) {
            UnionResult::Left(l) => (UnionResult::Left(UnionByLevel { rank: l, level: left.level }), l),
            UnionResult::Right(r) => (UnionResult::Right(UnionByLevel { rank: r, level: left.level }), r)
        };
        match left.level.cmp(&right.level) {
            Ordering::Less => UnionResult::Left(UnionByLevel { rank: rank, level: left.level }),
            Ordering::Greater => UnionResult::Right(UnionByLevel { rank: rank, level: right.level }),
            Ordering::Equal => rank_result
        }
    }
}

impl <T: fmt::Debug> fmt::Debug for Substitution<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Substitution {{ map: {:?}, named_variables: {:?}, var_id: {:?} }}",
               self.map.borrow(), self.named_variables.borrow(), self.var_id())
    }
}

impl <T> Substitution<T> {
    pub fn var_id(&self) -> u32 {
        (self.variables.borrow().len() - 1) as u32
    }
}

impl <T: Substitutable> Substitution<T> {
    pub fn new() -> Substitution<T> {
        let variables = FixedVec::new();
        variables.push(T::new(0));
        Substitution {
            map: RefCell::new(QuickFindUf::new(1)),
            variables: variables, 
            types: FixedMap::new(),
            named_variables: RefCell::new(HashMap::new()),
        }
    }

    pub fn clear(&mut self) {
        self.types.clear();
        self.variables.clear();
        self.variables.push(T::new(0));
        self.named_variables.borrow_mut().clear();
    }

    pub fn insert(&self, var: u32, t: T) {
        match t.get_var() {
            Some(_) => {
                panic!("Tried to insert variable which is not allowed as that would cause memory unsafety")
            }
            None => match self.types.try_insert(var, t) {
                Ok(()) => (),
                Err(_) => panic!("Expected variable to not have a type associated with it")
            }
        }
    }

    pub fn new_var(&self) -> T
    where T: Clone {
        let var_id = self.variables.len() as u32;
        let _id = self.map.borrow_mut().new_key();
        assert_eq!(_id, self.variables.len());
        self.variables.push(T::new(var_id));
        let last = self.variables.len() - 1;
        self.variables[last].clone()
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
        let index = self.map.borrow_mut().find(var as usize) as u32;
        self.types.get(&index)
            .or_else(|| if var == index { None } else { Some(&self.variables[index as usize]) })
    }

    pub fn variable_for(&self, id: InternedStr) -> T {
        let mut variables = self.named_variables.borrow_mut();
        match variables.entry(id) {
            Entry::Vacant(entry) => {
                let t = self.new_var();
                entry.insert(t).clone()
            }
            Entry::Occupied(entry) => entry.get().clone()
        }
    }

    pub fn update_level(&self, var: u32, other: u32) {
        let level = ::std::cmp::min(self.get_level(var), self.get_level(other));
        let mut map = self.map.borrow_mut();
        map.get_mut(var as usize).level = level;
        map.get_mut(other as usize).level = level;
    }

    pub fn get_level(&self, mut var: u32) -> u32 {
        if let Some(v) = self.find_type_for_var(var) {
            var = v.get_var().map(|v| v.get_id()).unwrap_or(var);
        }
        let mut map = self.map.borrow_mut();
        let level = &mut map.get_mut(var as usize).level;
        *level = ::std::cmp::min(*level, var);
        *level
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
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match typ.get_var() {
            Some(other_id) => {
                self.map.borrow_mut().union(id.get_id() as usize, other_id.get_id() as usize);
                self.update_level(id.get_id(), other_id.get_id());
            }
            _ => {
                self.insert(id.get_id(), typ.clone());
            }
        };
        Ok(())
    }

    pub fn set_var_id(&self, id: u32) {
        for _ in self.var_id()..id {
            self.new_var();
        }
    }
}
