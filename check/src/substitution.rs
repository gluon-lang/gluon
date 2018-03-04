use std::cell::RefCell;
use std::default::Default;
use std::fmt;

use union_find::{QuickFindUf, Union, UnionByRank, UnionFind, UnionResult};

use base::fnv::FnvMap;
use base::fixed::{FixedMap, FixedVec};
use base::types;
use base::types::{ArcType, Type, Walker};
use base::symbol::Symbol;

#[derive(Debug, PartialEq)]
pub enum Error<T> {
    Occurs(T, T),
}

impl<T> fmt::Display for Error<T>
where
    T: fmt::Display,
    T: for<'a> types::ToDoc<'a, ::pretty::Arena<'a>, ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match *self {
            Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
        }
    }
}

use typecheck::unroll_typ;

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
    /// stored here. As the type stored will never changed we use a `FixedMap` lets `real` return
    /// `&T` from this map safely.
    types: FixedMap<u32, T>,
    factory: T::Factory,
}

impl<T> Default for Substitution<T>
where
    T: Substitutable,
    T::Factory: Default,
{
    fn default() -> Substitution<T> {
        Substitution::new(Default::default())
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
    /// Constructs a new object from its variable type
    fn from_variable(x: Self::Variable) -> Self;
    /// Retrieves the variable if `self` is a variable otherwise returns `None`
    fn get_var(&self) -> Option<&Self::Variable>;
    fn traverse<'a, F>(&'a self, f: &mut F)
    where
        F: Walker<'a, Self>;
    fn instantiate(&self, subs: &Substitution<Self>) -> Self;

    fn on_union(&self) -> Option<&Self> {
        None
    }
}

pub fn occurs<T>(typ: &T, subs: &Substitution<T>, var: &T::Variable) -> bool
where
    T: Substitutable,
{
    struct Occurs<'a, T: Substitutable + 'a> {
        occurs: bool,
        var: &'a T::Variable,
        subs: &'a Substitution<T>,
    }
    impl<'a, 't, T> Walker<'t, T> for Occurs<'a, T>
    where
        T: Substitutable,
    {
        fn walk(&mut self, typ: &'t T) {
            if self.occurs {
                return;
            }
            let typ = self.subs.real(typ);
            if let Some(other) = typ.get_var() {
                if self.var.get_id() == other.get_id() {
                    self.occurs = true;
                    typ.traverse(self);
                    return;
                }
                self.subs.update_level(self.var.get_id(), other.get_id());
            }
            typ.traverse(self);
        }
    }
    let mut occurs = Occurs {
        occurs: false,
        var: var,
        subs: subs,
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

impl<T: Substitutable> Substitution<T> {
    pub fn new(factory: T::Factory) -> Substitution<T> {
        Substitution {
            union: RefCell::new(QuickFindUf::new(0)),
            variables: FixedVec::new(),
            types: FixedMap::new(),
            factory: factory,
        }
    }

    pub fn var_id(&self) -> u32 {
        self.variables.borrow().len() as u32
    }

    pub fn clear(&mut self) {
        self.types.clear();
        self.variables.clear();
    }

    pub fn insert(&self, var: u32, t: T) {
        match t.get_var() {
            Some(_) => ice!(
                "Tried to insert variable which is not allowed as that would cause memory \
                 unsafety"
            ),
            None => match self.types.try_insert(var, t) {
                Ok(()) => (),
                Err(_) => ice!("Expected variable to not have a type associated with it"),
            },
        }
    }

    /// Creates a new variable
    pub fn new_var(&self) -> T
    where
        T: Clone,
    {
        self.new_var_fn(|var| T::from_variable(self.factory.new(var)))
    }

    pub fn new_var_fn<F>(&self, f: F) -> T
    where
        T: Clone,
        F: FnOnce(u32) -> T,
    {
        let var_id = self.variables.len() as u32;
        let id = self.union.borrow_mut().insert(UnionByLevel {
            ..UnionByLevel::default()
        });
        assert!(id == self.variables.len());
        debug!("New var {}", self.variables.len());

        let var = f(var_id);
        self.variables.push(var.clone());
        var
    }

    /// If `typ` is a variable this returns the real unified value of that variable. Otherwise it
    /// just returns the type itself. Note that the returned type may contain terms which also need
    /// to have `real` called on them.
    pub fn real<'r>(&'r self, typ: &'r T) -> &'r T {
        match typ.get_var() {
            Some(var) => match self.find_type_for_var(var.get_id()) {
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
        let index = union.find(var as usize) as u32;
        self.types.get(&index).or_else(|| {
            if var == index {
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
        match typ.get_var() {
            Some(id) => self.find_type_for_var(id.get_id()).cloned(),
            None => None,
        }
    }
}

pub fn is_variable_unified(subs: &Substitution<ArcType>, var: &ArcType) -> bool {
    match **var {
        Type::Variable(ref var) => subs.find_type_for_var(var.id).is_some(),
        _ => unreachable!(),
    }
}

impl Substitution<ArcType> {
    fn replace_variable_(&self, typ: &Type<Symbol>) -> Option<ArcType> {
        match *typ {
            Type::Variable(ref id) => self.find_type_for_var(id.id).cloned(),
            _ => None,
        }
    }

    pub fn set_type(&self, t: ArcType) -> ArcType {
        self.set_type_(&t).unwrap_or(t)
    }
    fn set_type_(&self, typ: &ArcType) -> Option<ArcType> {
        match **typ {
            Type::Forall(ref params, ref typ, Some(ref vars)) => {
                let subs = self;
                let mut named_variables: FnvMap<_, _> = params
                    .iter()
                    .zip(vars)
                    .filter(|&(_, var)| is_variable_unified(subs, var))
                    .map(|(param, var)| (param.id.clone(), var.clone()))
                    .collect();
                let typ = typ.instantiate_generics(&mut named_variables);
                self.set_type_(&typ).map(|typ| {
                    if params.len() != named_variables.len() {
                        let mut new_params = Vec::new();
                        let mut new_vars = Vec::new();
                        for (param, var) in params.iter().zip(vars) {
                            if !is_variable_unified(subs, var) {
                                new_params.push(param.clone());
                                new_vars.push(var.clone());
                            }
                        }
                        ArcType::from(Type::Forall(new_params, typ, Some(new_vars)))
                    } else {
                        typ
                    }
                })
            }
            Type::Variable(_) => {
                let replacement = self.replace_variable_(typ);
                let result = {
                    let mut typ = typ;
                    if let Some(ref t) = replacement {
                        typ = t;
                    }
                    unroll_typ(typ)
                };
                result.or(replacement)
            }
            _ => types::walk_move_type_opt(
                typ,
                &mut types::ControlVisitation(|typ: &ArcType| self.set_type_(typ)),
            ),
        }
    }
}

impl<T: Substitutable + Clone> Substitution<T> {
    pub fn make_real(&self, typ: &mut T) {
        *typ = self.real(typ).clone();
    }
}
impl<T: Substitutable + PartialEq + Clone> Substitution<T> {
    /// Takes `id` and updates the substitution to say that it should have the same type as `typ`
    pub fn union(&self, id: &T::Variable, typ: &T) -> Result<Option<T>, Error<T>>
    where
        T::Variable: Clone,
        T: fmt::Display,
    {
        let resolved_type = typ.on_union();
        let typ = resolved_type.unwrap_or(typ);
        // Nothing needs to be done if both are the same variable already (also prevents the occurs
        // check from failing)
        if typ.get_var()
            .map_or(false, |other| other.get_id() == id.get_id())
        {
            return Ok(None);
        }
        if occurs(typ, self, id) {
            return Err(Error::Occurs(T::from_variable(id.clone()), typ.clone()));
        }
        {
            let id_type = self.find_type_for_var(id.get_id());
            let other_type = self.real(typ);
            if id_type.map_or(false, |x| x == other_type)
                || other_type.get_var().map(|y| y.get_id()) == Some(id.get_id())
            {
                return Ok(None);
            }
        }
        {
            let typ = resolved_type.unwrap_or(typ);
            match typ.get_var().map(|id| id.get_id()) {
                Some(other_id) => {
                    self.union
                        .borrow_mut()
                        .union(id.get_id() as usize, other_id as usize);
                    self.update_level(id.get_id(), other_id);
                    self.update_level(other_id, id.get_id());
                }
                _ => {
                    self.insert(id.get_id(), typ.clone());
                }
            }
        }
        Ok(resolved_type.cloned())
    }
}
