use std::{borrow::Borrow, fmt, mem, ops::Deref, rc::Rc};

use bitflags::bitflags;

use pretty::{Arena, DocBuilder};

use crate::base::{
    ast::Commented,
    fnv::FnvMap,
    metadata::Comment,
    pos::{BytePos, HasSpan, Span},
    source::Source,
    symbol::Symbol,
    types::{
        self, dt, forall_params, forall_params_vars, pretty_print::Printer, ArcType, Field,
        Generic, Prec, ToDoc, Type, TypeCache, TypeExt, TypeFormatter,
    },
};

bitflags! {
    pub struct Flags: u8 {
        const HAS_VARIABLES = 1 << 0;
        const HAS_SKOLEMS = 2 << 0;
    }
}

trait AddFlags {
    fn add_flags(&self, flags: &mut Flags);
}

impl<T> AddFlags for [T]
where
    T: AddFlags,
{
    fn add_flags(&self, flags: &mut Flags) {
        for t in self {
            t.add_flags(flags);
        }
    }
}

impl<Id, T> AddFlags for Field<Id, T>
where
    T: AddFlags,
{
    fn add_flags(&self, flags: &mut Flags) {
        self.typ.add_flags(flags);
    }
}

impl<Id> AddFlags for RcType<Id> {
    fn add_flags(&self, flags: &mut Flags) {
        *flags |= self.flags()
    }
}

impl<Id, T> AddFlags for Type<Id, T>
where
    T: AddFlags,
{
    fn add_flags(&self, flags: &mut Flags) {
        match self {
            Type::Function(_, arg, ret) => {
                arg.add_flags(flags);
                ret.add_flags(flags);
            }
            Type::App(ref f, ref args) => {
                f.add_flags(flags);
                args.add_flags(flags);
            }
            Type::Record(ref typ)
            | Type::Variant(ref typ)
            | Type::Effect(ref typ)
            | Type::Forall(_, ref typ, None) => typ.add_flags(flags),
            Type::Forall(_, ref typ, Some(_)) => {
                *flags |= Flags::HAS_SKOLEMS; // ?
                typ.add_flags(flags);
            }
            Type::Generic(_) // TODO Generics only need generalization if they are unbound
            | Type::Skolem(_) => *flags |= Flags::HAS_SKOLEMS,
            Type::ExtendRow { fields, rest, .. } => {
                fields.add_flags(flags);
                rest.add_flags(flags);
            }
            Type::Variable(_) => *flags |= Flags::HAS_VARIABLES,
            Type::Hole
            | Type::Opaque
            | Type::Error
            | Type::Builtin(..)
            | Type::Ident(_)
            | Type::Projection(_)
            | Type::Alias(_)
            | Type::EmptyRow => (),
        }
    }
}

impl Flags {
    fn from_type<Id, T>(typ: &Type<Id, T>) -> Self
    where
        T: AddFlags,
    {
        let mut flags = Flags::empty();
        typ.add_flags(&mut flags);
        flags
    }
}

#[derive(Eq, PartialEq, Hash)]
struct RcTypeInner<Id = Symbol> {
    typ: Type<Id, RcType<Id>>,
    flags: Flags,
}

#[derive(Eq, PartialEq, Hash)]
pub struct RcType<Id = Symbol> {
    typ: Rc<RcTypeInner<Id>>,
}

impl<Id> Default for RcType<Id> {
    fn default() -> Self {
        Type::hole()
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

impl<Id: AsRef<str>> fmt::Display for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", TypeFormatter::new(self))
    }
}

impl<Id> Borrow<Type<Id, RcType<Id>>> for RcType<Id> {
    fn borrow(&self) -> &Type<Id, RcType<Id>> {
        &self.typ.typ
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

impl<Id> From<Type<Id, RcType<Id>>> for RcType<Id> {
    fn from(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType::new(typ)
    }
}

impl<Id> TypeExt<Id> for RcType<Id> {
    fn new(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        let flags = Flags::from_type(&typ);
        RcType {
            typ: Rc::new(RcTypeInner { typ, flags }),
        }
    }
}

impl<Id> RcType<Id> {
    pub fn flags(&self) -> Flags {
        self.typ.flags
    }

    pub fn needs_generalize(&self) -> bool {
        self.flags()
            .intersects(Flags::HAS_VARIABLES | Flags::HAS_SKOLEMS)
    }

    pub fn forall_params_vars(&self) -> impl Iterator<Item = (&Generic<Id>, &Self)> {
        forall_params_vars(self)
    }

    pub fn forall_params(&self) -> impl Iterator<Item = &Generic<Id>> {
        forall_params(self)
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

pub fn translate_interned_type<T, U>(
    type_interner: &mut FnvMap<PtrEq<T>, U>,
    type_cache: &TypeCache<Symbol, U>,
    typ: &T,
) -> U
where
    T: Clone + Borrow<Type<Symbol, T>> + Deref<Target = Type<Symbol, T>>,
    U: From<Type<Symbol, U>> + Clone,
    PtrEq<T>: Borrow<PtrEq<Type<Symbol, T>, T>>,
{
    if let Some(t) = type_interner.get(PtrEq::new(typ)) {
        return t.clone();
    }
    let new_type = types::translate_type_with(type_cache, typ, |typ| {
        translate_interned_type(type_interner, type_cache, typ)
    });

    type_interner.insert(PtrEq(typ.clone(), Default::default()), new_type.clone());
    new_type
}
