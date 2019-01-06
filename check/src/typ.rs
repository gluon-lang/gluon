use std::{fmt, ops::Deref, rc::Rc};

use pretty::{Arena, DocBuilder};

use crate::base::{
    ast::Commented,
    metadata::Comment,
    pos::{BytePos, HasSpan, Span},
    source::Source,
    symbol::Symbol,
    types::{
        dt, forall_params, forall_params_vars, pretty_print::Printer, Generic, Prec, ToDoc, Type,
        TypeExt, TypeFormatter,
    },
};

#[derive(Eq, PartialEq, Hash)]
pub struct RcType<Id = Symbol> {
    typ: Rc<Type<Id, RcType<Id>>>,
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

impl<Id> Deref for RcType<Id> {
    type Target = Type<Id, RcType<Id>>;

    fn deref(&self) -> &Type<Id, RcType<Id>> {
        &self.typ
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
        RcType { typ: Rc::new(typ) }
    }
}

impl<Id> RcType<Id> {
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
