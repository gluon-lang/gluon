use std::{borrow::Borrow, fmt, hash::Hash, mem, ops::Deref, rc::Rc, sync::Arc};

use pretty::{Arena, DocBuilder};

use crate::base::{
    ast::Commented,
    fnv::FnvMap,
    metadata::Comment,
    pos::{BytePos, HasSpan, Span},
    source::Source,
    symbol::Symbol,
    types::{
        self, dt, forall_params, pretty_print::Printer, translate_alias, AliasData, AliasRef,
        ArcType, Generic, Prec, Skolem, ToDoc, Type, TypeExt, TypeFormatter, TypeInterner,
        TypeInternerAlloc,
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

#[doc(hidden)]
pub trait Ptr {
    type Target;
    fn as_ptr(&self) -> &Self::Target;
}

impl<T> Ptr for Arc<T> {
    type Target = T;
    fn as_ptr(&self) -> &Self::Target {
        self
    }
}

impl<T> Ptr for RcType<T> {
    type Target = Type<T, Self>;
    fn as_ptr(&self) -> &Self::Target {
        self
    }
}

impl<T> Ptr for ArcType<T> {
    type Target = Type<T, Self>;
    fn as_ptr(&self) -> &Self::Target {
        self
    }
}

impl<Id, T> Ptr for Type<Id, T> {
    type Target = Self;
    fn as_ptr(&self) -> &Self::Target {
        self
    }
}

#[repr(transparent)]
pub struct PtrEq<T>(pub T);

impl<T> PtrEq<T> {
    pub fn new(t: &T) -> &Self {
        unsafe { mem::transmute(t) }
    }
}

impl<T> Eq for PtrEq<T> where T: Ptr {}

impl<T> PartialEq for PtrEq<T>
where
    T: Ptr,
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq::<<T as Ptr>::Target>(self.0.as_ptr(), other.0.as_ptr())
    }
}

impl<T> std::hash::Hash for PtrEq<T>
where
    T: Ptr,
{
    #[inline(always)]
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0.as_ptr() as *const T::Target).hash(state)
    }
}

impl<T> Borrow<PtrEq<T>> for PtrEq<Arc<T>> {
    #[inline(always)]
    fn borrow(&self) -> &PtrEq<T> {
        PtrEq::new(self.0.as_ptr())
    }
}

impl Borrow<PtrEq<Type<Symbol, RcType>>> for PtrEq<RcType> {
    #[inline(always)]
    fn borrow(&self) -> &PtrEq<Type<Symbol, RcType>> {
        PtrEq::new(self.0.borrow())
    }
}

impl Borrow<PtrEq<Type<Symbol, ArcType>>> for PtrEq<ArcType> {
    #[inline(always)]
    fn borrow(&self) -> &PtrEq<Type<Symbol, ArcType>> {
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

pub struct TranslateInterner<T, U> {
    pub type_map: FnvMap<PtrEq<T>, U>,
    pub alias_map: FnvMap<PtrEq<Arc<Vec<AliasData<Symbol, T>>>>, Arc<Vec<AliasData<Symbol, U>>>>,
}

impl<T, U> Default for TranslateInterner<T, U>
where
    T: Ptr,
{
    fn default() -> Self {
        TranslateInterner {
            type_map: Default::default(),
            alias_map: Default::default(),
        }
    }
}

pub fn translate_interned_type<T, U>(
    type_interner: &mut TranslateInterner<T, U>,
    interner: &mut impl TypeInterner<Symbol, U>,
    typ: &T,
) -> U
where
    T: Clone + TypeExt<Id = Symbol>,
    U: Clone,
    PtrEq<T>: Eq + Hash,
{
    if T::strong_count(typ) == 1 {
        perform_translation(type_interner, interner, typ)
    } else {
        if let Some(t) = type_interner.type_map.get(PtrEq::new(typ)) {
            return t.clone();
        }
        let new_type = perform_translation(type_interner, interner, typ);

        type_interner
            .type_map
            .insert(PtrEq(typ.clone()), new_type.clone());
        new_type
    }
}

fn perform_translation<T, U>(
    type_interner: &mut TranslateInterner<T, U>,
    interner: &mut impl TypeInterner<Symbol, U>,
    typ: &T,
) -> U
where
    T: Clone + TypeExt<Id = Symbol>,
    U: Clone,
    PtrEq<T>: Eq + Hash,
{
    match **typ {
        Type::Alias(ref alias) => {
            let group = match type_interner.alias_map.get(PtrEq::new(&alias.group)) {
                Some(group) => group.clone(),
                None => {
                    let group = Arc::new(
                        alias
                            .group
                            .iter()
                            .map(|alias_data| {
                                translate_alias(alias_data, |a| {
                                    translate_interned_type(type_interner, interner, a)
                                })
                            })
                            .collect::<Vec<_>>(),
                    );
                    type_interner
                        .alias_map
                        .insert(PtrEq(alias.group.clone()), group.clone());
                    group
                }
            };

            interner.intern(Type::Alias(AliasRef::new(alias.index(), group)))
        }
        _ => types::translate_type_with(interner, typ, |interner, typ| {
            translate_interned_type(type_interner, interner, typ)
        }),
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
