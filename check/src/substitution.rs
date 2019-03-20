use std::{cell::RefCell, default::Default, fmt};

use union_find::{QuickFindUf, Union, UnionByRank, UnionFind, UnionResult};

use crate::base::{
    fixed::{FixedVec, FixedVecMap},
    kind::ArcKind,
    symbol::Symbol,
    types::{self, ArcType, Flags, FlagsVisitor, Skolem, Type, TypeContext, Walker},
};
use crate::typ::RcType;

#[derive(Debug, PartialEq, Functor)]
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
    union: RefCell<QuickFindUf<UnionByLevel>>,
    /// Vector containing all created variables for this substitution. Needed for the `real` method
    /// which needs to always be able to return a `&T` reference
    variables: FixedVec<T>,
    /// For variables which have been infered to have a real type (not a variable) their types are
    /// stored here. As the type stored will never changed we use a `FixedVecMap` lets `real` return
    /// `&T` from this map safely.
    types: FixedVecMap<T>,
    factory: T::Factory,
    interner: T::Interner,
    variable_cache: RefCell<Vec<T>>,
}

impl<T> TypeContext<Symbol, T> for Substitution<T>
where
    T: Substitutable + From<Type<Symbol, T>>,
    for<'a> &'a T::Interner: TypeContext<Symbol, T>,
{
    gluon_base::forward_type_interner_methods!(Symbol, T, self_, &self_.interner);
}

impl<'a, T> TypeContext<Symbol, T> for &'a Substitution<T>
where
    T: Substitutable + From<Type<Symbol, T>>,
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

    fn on_union(&self) -> Option<&Self> {
        None
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
    impl<'a, 't, T> Walker<'t, T> for Occurs<'a, T>
    where
        T: Substitutable,
    {
        fn walk(&mut self, typ: &'t T) {
            if !typ.contains_variables() || self.occurs {
                return;
            }
            let typ = self.subs.real(typ);
            if let Some(other) = typ.get_var() {
                if self.var.get_id() == other.get_id() {
                    self.occurs = true;
                    typ.traverse(self);
                    return;
                }
                self.subs.update_level(self.var, other.get_id());
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

/// Specialized union implementation which makes sure that variables with a higher level always
/// point to the lower level variable.
///
/// map.union(1, 2);
/// map.find(2) -> 1
/// map.find(1) -> 1
#[derive(Debug)]
struct UnionByLevel {
    rank: UnionByRank,
    level: u32,
}

impl Default for UnionByLevel {
    fn default() -> UnionByLevel {
        UnionByLevel {
            rank: UnionByRank::default(),
            level: ::std::u32::MAX,
        }
    }
}

impl Union for UnionByLevel {
    #[inline]
    fn union(left: UnionByLevel, right: UnionByLevel) -> UnionResult<UnionByLevel> {
        use std::cmp::Ordering;
        let (rank_result, rank) = match Union::union(left.rank, right.rank) {
            UnionResult::Left(l) => (
                UnionResult::Left(UnionByLevel {
                    rank: l,
                    level: left.level,
                }),
                l,
            ),
            UnionResult::Right(r) => (
                UnionResult::Right(UnionByLevel {
                    rank: r,
                    level: left.level,
                }),
                r,
            ),
        };
        match left.level.cmp(&right.level) {
            Ordering::Less => UnionResult::Left(UnionByLevel {
                rank: rank,
                level: left.level,
            }),
            Ordering::Greater => UnionResult::Right(UnionByLevel {
                rank: rank,
                level: right.level,
            }),
            Ordering::Equal => rank_result,
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
            union: RefCell::new(QuickFindUf::new(0)),
            variables: FixedVec::new(),
            types: FixedVecMap::new(),
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
            None => match self.types.try_insert(var as usize, t.into()) {
                Ok(()) => (),
                Err(_) => ice!("Expected variable to not have a type associated with it"),
            },
        }
    }

    pub fn replace(&mut self, var: u32, t: T) {
        debug_assert!(t.get_id() != Some(var));
        self.types.insert(var as usize, t.into());
    }

    pub fn reset(&mut self, var: u32) {
        self.types.remove(var as usize);
    }

    /// Assumes that no variables unified with anything (but variables < level may exist)
    pub fn clear_from(&mut self, level: u32) {
        self.union = RefCell::new(QuickFindUf::new(0));
        let mut u = self.union.borrow_mut();
        for _ in 0..level {
            u.insert(UnionByLevel {
                ..UnionByLevel::default()
            });
        }

        let mut variable_cache = self.variable_cache.borrow_mut();
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
        T: Clone,
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
        let id = self.union.borrow_mut().insert(UnionByLevel {
            level: var_id,
            ..UnionByLevel::default()
        });
        assert!(id == self.variables.len());
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
        if var as usize >= union.size() {
            return None;
        }
        let index = union.find(var as usize);
        self.types.get(index).or_else(|| {
            if var == index as u32 {
                None
            } else {
                Some(&self.variables[index as usize])
            }
        })
    }

    /// Updates the level of `other` to be the minimum level value of `var` and `other`
    pub fn update_level(&self, var: u32, other: u32) {
        let level = ::std::cmp::min(self.get_level(var), self.get_level(other));
        let mut union = self.union.borrow_mut();
        union.get_mut(other as usize).level = level;
    }

    pub fn set_level(&self, var: u32, level: u32) {
        let mut union = self.union.borrow_mut();
        union.get_mut(var as usize).level = level;
    }

    pub fn get_level(&self, mut var: u32) -> u32 {
        if let Some(v) = self.find_type_for_var(var) {
            var = v.get_var().map_or(var, |v| v.get_id());
        }
        let mut union = self.union.borrow_mut();
        let level = &mut union.get_mut(var as usize).level;
        *level = ::std::cmp::min(*level, var);
        *level
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
    pub fn union(&self, variable: &T, typ: &T) -> Result<Option<T>, Error<T>>
    where
        T::Variable: Clone,
        T: fmt::Display,
    {
        assert!(variable.get_id().is_some(), "Expected a variable");
        let id = variable.get_id().unwrap();

        let resolved_type = typ.on_union();
        let typ = resolved_type.unwrap_or(typ);
        // Nothing needs to be done if both are the same variable already (also prevents the occurs
        // check from failing)
        if typ.get_var().map_or(false, |other| other.get_id() == id) {
            return Ok(None);
        }
        if occurs(typ, self, id) {
            return Err(Error::Occurs(variable.clone(), typ.clone()));
        }
        {
            let id_type = self.find_type_for_var(id);
            let other_type = self.real(typ);
            if id_type.map_or(false, |x| x == other_type)
                || other_type.get_var().map(|y| y.get_id()) == Some(id)
            {
                return Ok(None);
            }
        }
        {
            let typ = resolved_type.unwrap_or(typ);
            match typ.get_var().map(|v| v.get_id()) {
                Some(other_id) if variable.get_var().is_some() => {
                    self.union
                        .borrow_mut()
                        .union(id as usize, other_id as usize);
                    self.update_level(id.get_id(), other_id);
                    self.update_level(other_id, id.get_id());
                }
                _ => {
                    if let Some(other_id) = typ.get_id() {
                        self.update_level(id.get_id(), other_id);
                    }
                    self.insert(id.get_id(), typ.clone());
                }
            }
        }
        Ok(resolved_type.cloned())
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
