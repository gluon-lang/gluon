use std::{cell::RefCell, default::Default, fmt};

use crate::base::{
    fixed::{FixedVec, FixedVecMap},
    kind::ArcKind,
    symbol::Symbol,
    types::{self, ArcType, Flags, FlagsVisitor, Skolem, Type, TypeContext, TypePtr, Walker},
};
use crate::typ::RcType;

#[derive(Debug, Eq, PartialEq, Hash, Clone, Functor)]
pub enum Error<T> {
    Occurs(T, T),
}

impl<T> fmt::Display for Error<T>
where
    T: fmt::Display,
    T: for<'a> types::ToDoc<'a, ::pretty::Arena<'a, ()>, (), ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match *self {
            Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
        }
    }
}

pub struct Substitution<T>
where
    T: Substitutable,
{
    /// Union-find data structure used to store the relationships of all variables in the
    /// substitution
    union: RefCell<ena::unify::InPlaceUnificationTable<UnionByLevel>>,
    /// Vector containing all created variables for this substitution. Needed for the `real` method
    /// which needs to always be able to return a `&T` reference
    variables: FixedVec<T>,
    /// For variables which have been infered to have a real type (not a variable) their types are
    /// stored here. As the type stored will never changed we use a `FixedVecMap` lets `real` return
    /// `&T` from this map safely.
    types: FixedVecMap<T>,
    types_undo: RefCell<Vec<u32>>,
    factory: T::Factory,
    interner: T::Interner,
    variable_cache: RefCell<Vec<T>>,
}

impl<T> TypeContext<Symbol, T> for Substitution<T>
where
    T: Substitutable + TypePtr<Id = Symbol> + From<Type<Symbol, T>>,
    for<'a> &'a T::Interner: TypeContext<Symbol, T>,
{
    gluon_base::forward_type_interner_methods!(Symbol, T, self_, &self_.interner);
}

impl<'a, T> TypeContext<Symbol, T> for &'a Substitution<T>
where
    T: Substitutable + TypePtr<Id = Symbol> + From<Type<Symbol, T>>,
    &'a T::Interner: TypeContext<Symbol, T>,
{
    gluon_base::forward_type_interner_methods!(Symbol, T, self_, &self_.interner);
}

impl<'a> types::Substitution<Symbol, RcType> for &'a Substitution<RcType> {
    fn new_var(&mut self) -> RcType {
        Substitution::new_var(*self)
    }
    fn new_skolem(&mut self, name: Symbol, kind: ArcKind) -> RcType {
        Substitution::new_skolem(*self, name, kind)
    }
}

impl<T> Default for Substitution<T>
where
    T: Substitutable,
    T::Factory: Default,
    T::Interner: Default,
{
    fn default() -> Substitution<T> {
        Substitution::new(Default::default(), Default::default())
    }
}

/// Trait which variables need to implement to allow the substitution to get to the u32 identifying
/// the variable
pub trait Variable {
    fn get_id(&self) -> u32;
}

impl Variable for u32 {
    fn get_id(&self) -> u32 {
        *self
    }
}

pub trait VariableFactory {
    type Variable: Variable;

    fn new(&self, x: u32) -> Self::Variable;
}

impl VariableFactory for () {
    type Variable = u32;

    fn new(&self, x: u32) -> Self::Variable {
        x
    }
}

/// Trait implemented on types which may contain substitutable variables
pub trait Substitutable: Sized {
    type Variable: Variable;

    type Factory: VariableFactory<Variable = Self::Variable>;

    type Interner: Default;

    /// Constructs a new object from its variable type
    fn from_variable(subs: &Substitution<Self>, x: Self::Variable) -> Self;

    fn into_variable(&mut self, x: Self::Variable);

    fn is_unique(self_: &Self) -> bool;

    /// Retrieves the variable if `self` is a variable otherwise returns `None`
    fn get_var(&self) -> Option<&Self::Variable>;

    fn get_id(&self) -> Option<u32> {
        self.get_var().map(|var| var.get_id())
    }

    fn traverse<'a, F>(&'a self, f: &mut F)
    where
        F: Walker<'a, Self>;

    fn instantiate(&self, subs: &Substitution<Self>) -> Self;

    // Allowed return true even if the type does not contain variables but not false if it does
    // contain
    fn contains_variables(&self) -> bool {
        true
    }
}

pub fn occurs<T>(typ: &T, subs: &Substitution<T>, var: u32) -> bool
where
    T: Substitutable,
{
    struct Occurs<'a, T: Substitutable + 'a> {
        occurs: bool,
        var: u32,
        subs: &'a Substitution<T>,
    }
    impl<'t, T> Walker<'t, T> for Occurs<'t, T>
    where
        T: Substitutable,
    {
        fn walk(&mut self, mut typ: &'t T) {
            if !typ.contains_variables() {
                return;
            }
            if let Some(other) = typ.get_var() {
                let other_id = other.get_id();
                if let Some(real_type) = self.subs.find_type_for_var(other_id) {
                    typ = real_type;
                } else {
                    if self.var.get_id() == other_id {
                        self.occurs = true;
                        typ.traverse(self);
                        return;
                    }
                    self.subs.update_level(self.var, other.get_id());
                }
            }
            typ.traverse(self);
        }
    }

    let mut occurs = Occurs {
        occurs: false,
        var,
        subs,
    };
    occurs.walk(typ);
    occurs.occurs
}

pub struct Snapshot {
    snapshot: ena::unify::Snapshot<ena::unify::InPlace<UnionByLevel>>,
    level: u32,
    types_undo_len: usize,
}

/// Specialized union implementation which makes sure that variables with a higher level always
/// point to the lower level variable.
///
/// map.union(1, 2);
/// map.find(2) -> 1
/// map.find(1) -> 1
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct UnionByLevel {
    index: u32,
}

impl From<u32> for UnionByLevel {
    fn from(index: u32) -> Self {
        ena::unify::UnifyKey::from_index(index)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(u32);

impl ena::unify::UnifyValue for Level {
    type Error = ena::unify::NoError;
    fn unify_values(l: &Self, r: &Self) -> Result<Self, Self::Error> {
        Ok(*l.min(r))
    }
}

impl ena::unify::UnifyKey for UnionByLevel {
    type Value = Level;

    fn index(&self) -> u32 {
        self.index
    }

    fn from_index(index: u32) -> Self {
        Self { index }
    }

    fn tag() -> &'static str {
        "UnionByLevel"
    }

    #[inline]
    fn order_roots(a: Self, a_level: &Level, b: Self, b_level: &Level) -> Option<(Self, Self)> {
        use std::cmp::Ordering;
        match a_level.cmp(&b_level) {
            Ordering::Less => Some((a, b)),
            Ordering::Greater => Some((b, a)),
            Ordering::Equal => None,
        }
    }
}

impl<T> fmt::Debug for Substitution<T>
where
    T: fmt::Debug + Substitutable,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Substitution {{ map: {:?}, var_id: {:?} }}",
            self.union.borrow(),
            self.var_id()
        )
    }
}

impl<T> Substitution<T>
where
    T: Substitutable,
{
    pub fn new(factory: T::Factory, interner: T::Interner) -> Substitution<T> {
        Substitution {
            union: RefCell::new(ena::unify::InPlaceUnificationTable::new()),
            variables: FixedVec::new(),
            types: FixedVecMap::new(),
            types_undo: Default::default(),
            factory: factory,
            interner,
            variable_cache: Default::default(),
        }
    }

    pub fn var_id(&self) -> u32 {
        self.variables.len() as u32
    }

    pub fn insert(&self, var: u32, t: T) {
        match t.get_var() {
            Some(_) => ice!(
                "Tried to insert variable which is not allowed as that would cause memory \
                 unsafety"
            ),
            None => {
                self.types_undo.borrow_mut().push(var);
                match self.types.try_insert(var as usize, t.into()) {
                    Ok(()) => (),
                    Err(_) => ice!("Expected variable to not have a type associated with it"),
                }
            }
        }
    }

    pub fn replace(&mut self, var: u32, t: T) {
        debug_assert!(t.get_id() != Some(var));
        self.types_undo.get_mut().push(var);
        self.types.insert(var as usize, t.into());
    }

    pub fn reset(&mut self, var: u32) {
        self.types.remove(var as usize);
    }

    pub fn snapshot(&mut self) -> Snapshot {
        Snapshot {
            snapshot: self.union.get_mut().snapshot(),
            level: self.var_id(),
            types_undo_len: self.types_undo.get_mut().len(),
        }
    }

    pub fn commit(&mut self, snapshot: Snapshot) {
        self.union.get_mut().commit(snapshot.snapshot);
    }

    pub fn rollback_to(&mut self, snapshot: Snapshot) {
        self.union.get_mut().rollback_to(snapshot.snapshot);
        let variable_cache = self.variable_cache.get_mut();
        while self.variables.len() > snapshot.level as usize {
            variable_cache.push(self.variables.pop().unwrap());
        }

        for i in self.types_undo.get_mut().drain(snapshot.types_undo_len..) {
            self.types.remove(i as usize);
        }
    }

    /// Assumes that no variables unified with anything (but variables < level may exist)
    pub fn clear_from(&mut self, level: u32) {
        self.union = RefCell::new(ena::unify::InPlaceUnificationTable::new());
        let u = self.union.get_mut();
        for var in 0..level {
            u.new_key(Level(var));
        }

        let variable_cache = self.variable_cache.get_mut();
        // Since no types should be unified with anything we can remove all of this and reuse the
        // unique values
        variable_cache.extend(self.types.drain().filter(T::is_unique));
        while self.variables.len() > level as usize {
            variable_cache.push(self.variables.pop().unwrap());
        }
    }

    /// Creates a new variable
    pub fn new_var(&self) -> T
    where
        T: Clone + fmt::Display,
    {
        self.new_var_fn(|var| match self.variable_cache.borrow_mut().pop() {
            Some(mut typ) => {
                T::into_variable(&mut typ, self.factory.new(var));
                typ
            }
            None => T::from_variable(self, self.factory.new(var)),
        })
    }

    pub fn new_var_fn<F>(&self, f: F) -> T
    where
        T: Clone,
        F: FnOnce(u32) -> T,
    {
        let var_id = self.variables.len() as u32;
        let id = self.union.borrow_mut().new_key(Level(var_id)).index;
        assert!(id as usize == self.variables.len());
        debug!("New var {}", self.variables.len());

        let var = f(var_id);
        self.variables.push(var.clone().into());
        var
    }

    /// If `typ` is a variable this returns the real unified value of that variable. Otherwise it
    /// just returns the type itself. Note that the returned type may contain terms which also need
    /// to have `real` called on them.
    pub fn real<'r>(&'r self, typ: &'r T) -> &'r T {
        match typ.get_id() {
            Some(id) => match self.find_type_for_var(id) {
                Some(t) => t,
                None => typ,
            },
            _ => typ,
        }
    }

    pub fn get_var(&self, var: u32) -> Option<&T> {
        self.variables.get(var as usize)
    }

    pub fn find_type_for_var(&self, var: u32) -> Option<&T> {
        let mut union = self.union.borrow_mut();
        if var as usize >= union.len() {
            return None;
        }
        let index = union.find(var).index;
        self.types.get(index as usize).or_else(|| {
            if var == index as u32 {
                None
            } else {
                Some(&self.variables[index as usize])
            }
        })
    }

    /// Updates the level of `other` to be the minimum level value of `var` and `other`
    fn update_level(&self, var: u32, other: u32) {
        let mut union = self.union.borrow_mut();
        let level = union.probe_value(var).min(union.probe_value(other));
        union.union_value(other, level);
    }

    pub fn get_level(&self, var: u32) -> u32 {
        let mut union = self.union.borrow_mut();
        union.probe_value(var).0
    }

    pub fn replace_variable(&self, typ: &T) -> Option<T>
    where
        T: Clone,
    {
        match typ.get_id() {
            Some(id) => self.find_type_for_var(id).cloned(),
            None => None,
        }
    }
}

pub fn is_variable_unified(subs: &Substitution<RcType>, var: &RcType) -> bool {
    match **var {
        Type::Variable(ref var) => subs.find_type_for_var(var.id).is_some(),
        _ => false,
    }
}

impl<T: Substitutable + Clone> Substitution<T> {
    pub fn make_real(&self, typ: &mut T) {
        *typ = self.real(typ).clone();
    }
}

impl<T: Substitutable + PartialEq + Clone> Substitution<T> {
    /// Takes `id` and updates the substitution to say that it should have the same type as `typ`
    pub fn union(&self, variable: &T, typ: &T) -> Result<(), Error<T>>
    where
        T::Variable: Clone,
        T: fmt::Display,
    {
        assert!(variable.get_id().is_some(), "Expected a variable");
        let id = variable.get_id().unwrap();

        match typ.get_var() {
            Some(other_var) if variable.get_var().is_some() => {
                self.union.borrow_mut().union(id, other_var.get_id());
            }
            _ => {
                if occurs(typ, self, id) {
                    return Err(Error::Occurs(variable.clone(), typ.clone()));
                }
                self.insert(id.get_id(), typ.clone());
            }
        }
        Ok(())
    }
}

impl Substitution<RcType> {
    pub fn new_skolem(&self, name: Symbol, kind: ArcKind) -> RcType {
        self.new_var_fn(|id| {
            let skolem = Skolem { name, id, kind };
            match self.variable_cache.borrow_mut().pop() {
                Some(mut typ) => {
                    RcType::set(&mut typ, Type::Skolem(skolem));
                    typ
                }
                None => (&*self).skolem(skolem),
            }
        })
    }

    pub fn zonk(&self, typ: &RcType) -> RcType {
        types::walk_move_type(
            typ.clone(),
            &mut FlagsVisitor(Flags::HAS_VARIABLES, |typ: &RcType| match typ.get_id() {
                Some(id) => match self.find_type_for_var(id) {
                    Some(t) => Some(self.zonk(t)),
                    None => None,
                },
                None => None,
            }),
        )
    }

    // Stub kept in case multiple types are attempted again
    pub fn bind_arc(&self, typ: &RcType) -> ArcType {
        typ.clone()
    }
}
