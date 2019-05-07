use std::{fmt, ops};

use base::types::ArcType;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeModifier {
    Wobbly,
    Rigid,
}

impl Default for TypeModifier {
    fn default() -> Self {
        TypeModifier::Wobbly
    }
}

impl ops::BitOr for TypeModifier {
    type Output = Self;

    fn bitor(mut self, typ: Self) -> Self {
        self |= typ;
        self
    }
}
impl ops::BitOrAssign for TypeModifier {
    fn bitor_assign(&mut self, typ: Self) {
        match (*self, typ) {
            (TypeModifier::Rigid, TypeModifier::Rigid) => (),
            _ => *self = TypeModifier::Wobbly,
        }
    }
}

pub type ModTypeRef<'a> = ModType<&'a ArcType>;

#[derive(Clone, Copy, Debug)]
pub struct ModType<T = ArcType> {
    pub modifier: TypeModifier,
    pub concrete: T,
}

impl<T> fmt::Display for ModType<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.concrete.fmt(f)
    }
}

impl<T> ops::Deref for ModType<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.concrete
    }
}

impl<T> ops::DerefMut for ModType<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.concrete
    }
}

impl<T> ops::BitOrAssign for ModType<T> {
    fn bitor_assign(&mut self, typ: Self) {
        self.modifier |= typ.modifier;
        self.concrete = typ.concrete;
    }
}

impl<T> ModType<T> {
    pub fn new(modifier: TypeModifier, typ: T) -> Self {
        ModType {
            modifier,
            concrete: typ,
        }
    }

    pub fn rigid(typ: T) -> Self {
        Self::new(TypeModifier::Rigid, typ)
    }

    pub fn wobbly(typ: T) -> Self {
        Self::new(TypeModifier::Wobbly, typ)
    }

    pub fn as_ref(&self) -> ModType<&T> {
        ModType::new(self.modifier, &self.concrete)
    }
}

impl<'a, T> ModType<&'a T>
where
    T: Clone,
{
    pub fn to_owned(&self) -> ModType<T> {
        ModType::new(self.modifier, self.concrete.clone())
    }
}
