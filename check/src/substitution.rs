use std::cell::RefCell;
use std::default::Default;
use std::fmt;
use union_find::{QuickFindUf, Union, UnionByRank, UnionFind, UnionResult};
use base::fixed::{FixedMap, FixedVec};

pub struct Substitution<T> {
    ///Union-find data structure used to store the relationships of all variables in the
    ///substitution
    union: RefCell<QuickFindUf<UnionByLevel>>,
    ///Vector containing all created variables for this substitution. Needed for the `real` method
    ///which needs to always be able to return a `&T` reference
    variables: FixedVec<T>,
    ///For variables which have been infered to have a real type (not a variable) their types are
    ///stored here. As the type stored will never changed we use a `FixedMap` lets `real` return
    ///`&T` from this map safely.
    types: FixedMap<u32, T>,
}

///Trait which variables need to implement to allow the substitution to get to the u32 identifying
///the variable
pub trait Variable {
    fn get_id(&self) -> u32;
}

impl Variable for u32 {
    fn get_id(&self) -> u32 {
        *self
    }
}

///Trait implemented on types which may contain substitutable variables
pub trait Substitutable: PartialEq + Clone {
    type Variable: Variable;
    fn new(x: u32) -> Self;
    ///Constructs a new object from its variable type
    fn from_variable(x: Self::Variable) -> Self;
    ///Retrieves the variable if `self` is a variable otherwise returns `None`
    fn get_var(&self) -> Option<&Self::Variable>;
    ///Returns whether `var` occurs somewhere in `self`
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
        write!(f, "Substitution {{ map: {:?}, var_id: {:?} }}",
               self.union.borrow(), self.var_id())
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
        //0 is the default, uninitialized variable so we add it to make sure that the first
        //variable we create through `new_var` is 1
        variables.push(T::new(0));
        Substitution {
            union: RefCell::new(QuickFindUf::new(1)),
            variables: variables, 
            types: FixedMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.types.clear();
        self.variables.clear();
        self.variables.push(T::new(0));
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

    ///Creates a new variable
    pub fn new_var(&self) -> T
    where T: Clone {
        let var_id = self.variables.len() as u32;
        let _id = self.union.borrow_mut().insert(UnionByLevel::default());
        assert_eq!(_id, self.variables.len());
        self.variables.push(T::new(var_id));
        let last = self.variables.len() - 1;
        self.variables[last].clone()
    }

    ///If `typ` is a variable this returns the real unified value of that variable. Otherwise it
    ///just returns the type itself. Note that the returned type may contain terms which also need
    ///to have `real` called on them.
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
        *typ = self.real(typ).clone();
    }

    pub fn find_type_for_var(&self, var: u32) -> Option<&T> {
        let index = self.union.borrow_mut().find(var as usize) as u32;
        self.types.get(&index)
            .or_else(|| if var == index { None } else { Some(&self.variables[index as usize]) })
    }

    ///Updates the level of `other` to be the minimum level value of `var` and `other`
    pub fn update_level(&self, var: u32, other: u32) {
        let level = ::std::cmp::min(self.get_level(var), self.get_level(other));
        let mut union = self.union.borrow_mut();
        union.get_mut(other as usize).level = level;
    }

    pub fn get_level(&self, mut var: u32) -> u32 {
        if let Some(v) = self.find_type_for_var(var) {
            var = v.get_var().map(|v| v.get_id()).unwrap_or(var);
        }
        let mut union = self.union.borrow_mut();
        let level = &mut union.get_mut(var as usize).level;
        *level = ::std::cmp::min(*level, var);
        *level
    }

    ///Takes `id` and updates the substitution to say that it should have the same type as `typ`
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
        match typ.get_var() {
            Some(other_id) => {
                self.union.borrow_mut().union(id.get_id() as usize, other_id.get_id() as usize);
                self.update_level(id.get_id(), other_id.get_id());
                self.update_level(other_id.get_id(), id.get_id());
            }
            _ => {
                self.insert(id.get_id(), typ.clone());
            }
        };
        Ok(())
    }
}
