use super::{Field, FlagsVisitor, Type, TypeExt, Walker};

use bitflags::bitflags;

bitflags! {
    #[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
    pub struct Flags: u8 {
        const HAS_VARIABLES = 1 << 0;
        const HAS_SKOLEMS = 1 << 1;
        const HAS_GENERICS = 1 << 2;
        const HAS_FORALL = 1 << 3;
        const HAS_IDENTS = 1 << 4;
        const HAS_IMPLICIT = 1 << 5;


        const NEEDS_GENERALIZE =
            Flags::HAS_VARIABLES.bits | Flags::HAS_SKOLEMS.bits;
    }
}

pub(crate) trait AddFlags {
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

impl<T> AddFlags for T
where
    T: TypeExt,
{
    fn add_flags(&self, flags: &mut Flags) {
        *flags |= self.flags()
    }
}

impl<Id, T> AddFlags for Type<Id, T>
where
    T: AddFlags + TypeExt<Id = Id>,
    Id: PartialEq,
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
            Type::Record(ref typ) | Type::Variant(ref typ) | Type::Effect(ref typ) => {
                typ.add_flags(flags)
            }
            Type::Forall(ref params, ref typ) => {
                *flags |= Flags::HAS_FORALL;
                typ.add_flags(flags);

                let mut unbound_generic = false;
                &mut FlagsVisitor(Flags::HAS_GENERICS, |typ: &T| match &**typ {
                    Type::Generic(gen) => {
                        unbound_generic |= params.iter().all(|param| param.id != gen.id)
                    }
                    _ => (),
                })
                .walk(typ);
                if !unbound_generic {
                    flags.remove(Flags::HAS_GENERICS);
                }
            }
            Type::Skolem(_) => *flags |= Flags::HAS_SKOLEMS,
            Type::ExtendRow { fields, rest } => {
                fields[..].add_flags(flags);
                rest.add_flags(flags);
            }
            Type::ExtendTypeRow { rest, .. } => {
                rest.add_flags(flags);
            }
            Type::Variable(_) => *flags |= Flags::HAS_VARIABLES,
            Type::Generic(_) => *flags |= Flags::HAS_GENERICS,
            Type::Ident(_) => *flags |= Flags::HAS_IDENTS,
            Type::Hole
            | Type::Opaque
            | Type::Error
            | Type::Builtin(..)
            | Type::Projection(_)
            | Type::Alias(_)
            | Type::EmptyRow => (),
        }
    }
}

impl Flags {
    pub fn from_type<Id, T>(typ: &Type<Id, T>) -> Self
    where
        T: TypeExt + TypeExt<Id = Id>,
        Id: PartialEq,
    {
        let mut flags = Flags::empty();
        typ.add_flags(&mut flags);
        flags
    }
}
