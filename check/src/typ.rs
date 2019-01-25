use std::{borrow::Borrow, fmt, hash::Hash, mem, ops::Deref, rc::Rc};

use pretty::{Arena, DocBuilder};

use crate::base::{
    ast::Commented,
    fnv::FnvMap,
    metadata::Comment,
    pos::{BytePos, HasSpan, Span},
    source::Source,
    symbol::Symbol,
    types::{
        self, dt, forall_params, pretty_print::Printer, ArcType, Generic, Prec, Skolem, ToDoc,
        Type, TypeExt, TypeFormatter, TypeInterner, TypeInternerAlloc,
    },
};

use crate::substitution::Substitution;

pub use crate::base::types::Flags;

#[derive(Clone)]
struct RcTypeInner<Id = Symbol> {
    typ: Type<Id, RcType<Id>>,
    flags: Flags,
}

pub struct RcType<Id = Symbol> {
    typ: Rc<RcTypeInner<Id>>,
}

// FIXME Remove this as it is not an interned type
impl<Id> Default for RcType<Id> {
    fn default() -> Self {
        RcType::new(Type::Hole)
    }
}

impl<Id> Eq for RcType<Id> {}

impl<Id> PartialEq for RcType<Id> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq::<RcTypeInner<_>>(&*self.typ, &*other.typ)
    }
}

impl<Id> std::hash::Hash for RcType<Id> {
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (&*self.typ as *const RcTypeInner<_>).hash(state)
    }
}

impl<Id> Clone for RcType<Id> {
    fn clone(&self) -> RcType<Id> {
        RcType {
            typ: self.typ.clone(),
        }
    }
}

impl<Id: fmt::Debug> fmt::Debug for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id> fmt::Pointer for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:p}", &**self)
    }
}

impl<Id: AsRef<str>> fmt::Display for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", TypeFormatter::new(self))
    }
}

impl<Id> Deref for RcType<Id> {
    type Target = Type<Id, RcType<Id>>;

    fn deref(&self) -> &Type<Id, RcType<Id>> {
        &self.typ.typ
    }
}

impl<Id> HasSpan for RcType<Id> {
    fn span(&self) -> Span<BytePos> {
        Span::new(0.into(), 0.into())
    }
}

impl<Id> Commented for RcType<Id> {
    fn comment(&self) -> Option<&Comment> {
        None
    }
}

// TODO Remove this to prevent accidental construction if non interned types
impl<Id> From<Type<Id, RcType<Id>>> for RcType<Id> {
    fn from(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType::new(typ)
    }
}

impl<Id> TypeExt for RcType<Id> {
    type Id = Id;

    fn new(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        let flags = Flags::from_type(&typ);
        RcType {
            typ: Rc::new(RcTypeInner { typ, flags }),
        }
    }

    fn strong_count(typ: &Self) -> usize {
        Rc::strong_count(&typ.typ)
    }

    #[inline(always)]
    fn flags(&self) -> Flags {
        self.typ.flags
    }
}

impl<Id> RcType<Id> {
    pub fn needs_generalize(&self) -> bool {
        self.flags().intersects(Flags::NEEDS_GENERALIZE)
    }

    pub fn forall_params(&self) -> impl Iterator<Item = &Generic<Id>> {
        forall_params(self)
    }
}

impl RcType {
    pub fn instantiate_generics(
        &self,
        interner: &mut &Substitution<Self>,
        named_variables: &mut FnvMap<Symbol, Self>,
    ) -> Self {
        let mut typ = self;
        while let Type::Forall(params, inner_type) = &**typ {
            named_variables.extend(
                params
                    .iter()
                    .map(|param| (param.id.clone(), interner.new_var())),
            );
            typ = inner_type;
        }
        if named_variables.is_empty() {
            typ.clone()
        } else {
            typ.replace_generics(interner, named_variables)
                .unwrap_or_else(|| typ.clone())
        }
    }

    pub fn skolemize(
        &self,
        interner: &mut &Substitution<Self>,
        named_variables: &mut FnvMap<Symbol, Self>,
    ) -> Self {
        let mut typ = self;
        while let Type::Forall(ref params, ref inner_type) = **typ {
            let iter = params.iter().map(|param| {
                let var = interner.new_var(); // TODO Avoid allocating a variable
                let var = var.as_variable().unwrap();
                (
                    param.id.clone(),
                    interner.intern(Type::Skolem(Skolem {
                        name: param.id.clone(),
                        id: var.id,
                        kind: var.kind.clone(),
                    })),
                )
            });
            named_variables.extend(iter);
            typ = inner_type;
        }
        if named_variables.is_empty() {
            typ.clone()
        } else {
            typ.replace_generics(interner, named_variables)
                .unwrap_or_else(|| typ.clone())
        }
    }

    pub fn skolemize_in(
        &self,
        interner: &mut &Substitution<Self>,
        named_variables: &mut FnvMap<Symbol, Self>,
        f: impl FnOnce(Self) -> Self,
    ) -> Self {
        let skolemized = self.skolemize(interner, named_variables);
        let new_type = f(skolemized);
        interner.with_forall(new_type, self)
    }
}

impl<'a, I, A> ToDoc<'a, Arena<'a, A>, A, ()> for RcType<I>
where
    I: AsRef<str>,
    A: Clone,
{
    fn to_doc(&'a self, arena: &'a Arena<'a, A>, _: ()) -> DocBuilder<'a, Arena<'a, A>, A> {
        self.to_doc(arena, &() as &Source)
    }
}

impl<'a, I, A> ToDoc<'a, Arena<'a, A>, A, &'a Source> for RcType<I>
where
    I: AsRef<str>,
    A: Clone,
{
    fn to_doc(
        &'a self,
        arena: &'a Arena<'a, A>,
        source: &'a Source,
    ) -> DocBuilder<'a, Arena<'a, A>, A> {
        let printer = Printer::new(arena, source);
        dt(Prec::Top, self).pretty(&printer)
    }
}

#[repr(transparent)]
pub struct PtrEq<T, U = T>(pub T, pub std::marker::PhantomData<U>);

impl<T> PtrEq<Type<Symbol, T>, T> {
    pub fn new(t: &Type<Symbol, T>) -> &Self {
        unsafe { mem::transmute(t) }
    }
}

impl<T, U> Eq for PtrEq<T, U> where T: Borrow<Type<Symbol, U>> {}

impl<T, U> PartialEq for PtrEq<T, U>
where
    T: Borrow<Type<Symbol, U>>,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq::<Type<_, _>>(self.0.borrow(), other.0.borrow())
    }
}

impl<T, U> std::hash::Hash for PtrEq<T, U>
where
    T: Borrow<Type<Symbol, U>>,
{
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0.borrow() as *const Type<_, _>).hash(state)
    }
}

impl Borrow<PtrEq<Type<Symbol, RcType>, RcType>> for PtrEq<RcType, RcType> {
    #[inline(always)]
    fn borrow(&self) -> &PtrEq<Type<Symbol, RcType>, RcType> {
        PtrEq::new(self.0.borrow())
    }
}

impl Borrow<PtrEq<Type<Symbol, ArcType>, ArcType>> for PtrEq<ArcType, ArcType> {
    #[inline(always)]
    fn borrow(&self) -> &PtrEq<Type<Symbol, ArcType>, ArcType> {
        PtrEq::new(self.0.borrow())
    }
}

impl TypeInternerAlloc for RcType {
    type Id = Symbol;
    fn alloc(into: &mut Self, typ: Type<Symbol, Self>) {
        match Rc::get_mut(&mut into.typ) {
            Some(into) => {
                into.flags = Flags::from_type(&typ);
                into.typ = typ;
            }
            None => {
                *into = RcType::new(typ);
            }
        }
    }
}

pub fn translate_interned_type<T, U>(
    type_interner: &mut FnvMap<PtrEq<T>, U>,
    interner: &mut impl TypeInterner<Symbol, U>,
    typ: &T,
) -> U
where
    T: Clone + Borrow<Type<Symbol, T>> + TypeExt<Id = Symbol>,
    U: Clone,
    PtrEq<T>: Borrow<PtrEq<Type<Symbol, T>, T>>,
{
    if T::strong_count(typ) == 1 {
        types::translate_type_with(interner, typ, |interner, typ| {
            translate_interned_type(type_interner, interner, typ)
        })
    } else {
        if let Some(t) = type_interner.get(PtrEq::new(typ)) {
            return t.clone();
        }
        let new_type = types::translate_type_with(interner, typ, |interner, typ| {
            translate_interned_type(type_interner, interner, typ)
        });

        type_interner.insert(PtrEq(typ.clone(), Default::default()), new_type.clone());
        new_type
    }
}

pub fn translate_rc_interned_type<T, U>(
    type_interner: &mut FnvMap<T, U>,
    interner: &mut impl TypeInterner<Symbol, U>,
    typ: &T,
) -> U
where
    T: Clone + TypeExt<Id = Symbol> + Eq + Hash,
    U: Clone,
{
    if T::strong_count(typ) == 1 {
        types::translate_type_with(interner, typ, |interner, typ| {
            translate_rc_interned_type(type_interner, interner, typ)
        })
    } else {
        if let Some(t) = type_interner.get(typ) {
            return t.clone();
        }
        let new_type = types::translate_type_with(interner, typ, |interner, typ| {
            translate_rc_interned_type(type_interner, interner, typ)
        });

        type_interner.insert(typ.clone(), new_type.clone());
        new_type
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags() {
        let gen = Type::<_, RcType>::generic(Generic::new(Symbol::from("a"), Default::default()));
        assert_eq!(gen.flags(), Flags::HAS_GENERICS);
        assert_eq!(
            Type::function(vec![gen.clone()], gen.clone()).flags(),
            Flags::HAS_GENERICS
        );
    }
}
