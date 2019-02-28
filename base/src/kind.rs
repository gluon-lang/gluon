use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use pretty::{DocAllocator, DocBuilder};

use crate::ast::EmptyEnv;
use crate::symbol::{Symbol, SymbolRef};
use crate::types::{ToDoc, Walker};

/// Trait for values which contains kinded values which can be referred by name
pub trait KindEnv {
    /// Returns the kind of the type `type_name`
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind>;
}

impl<'a, T: ?Sized + KindEnv> KindEnv for &'a T {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        (**self).find_kind(id)
    }
}

impl KindEnv for EmptyEnv<Symbol> {
    fn find_kind(&self, _id: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

/// Kind representation
///
/// All types in gluon has a kind. Most types encountered are of the `Type` kind which
/// includes things like `Int`, `String` and `Option Int`. There are however other types
/// which are said to be "higher kinded" and these use the `Function` (a -> b) variant.
/// These types include `Option` and `(->)` which both have the kind `Type -> Type -> Type`
/// as well as `Functor` which has the kind `Type -> Type -> Type`.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "S"))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "S"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "S: AsMut<crate::serialization::NodeMap>"))
)]
pub enum Kind {
    Hole,
    Error,
    /// Representation for a kind which is yet to be inferred.
    Variable(u32),
    /// The simplest possible kind. All values in a program have this kind.
    Type,
    /// Kinds of rows (for polymorphic records).
    Row,
    /// Constructor which takes two kinds, taking the first as argument and returning the second.
    Function(
        #[cfg_attr(feature = "serde_derive", serde(state))] ArcKind,
        #[cfg_attr(feature = "serde_derive", serde(state))] ArcKind,
    ),
}

impl Default for Kind {
    fn default() -> Self {
        Kind::Hole
    }
}

impl Kind {
    pub fn hole() -> ArcKind {
        ArcKind::new(Kind::Hole)
    }

    pub fn error() -> ArcKind {
        ArcKind::new(Kind::Error)
    }

    pub fn variable(v: u32) -> ArcKind {
        ArcKind::new(Kind::Variable(v))
    }

    pub fn typ() -> ArcKind {
        ArcKind::new(Kind::Type)
    }

    pub fn row() -> ArcKind {
        ArcKind::new(Kind::Row)
    }

    pub fn function(l: ArcKind, r: ArcKind) -> ArcKind {
        ArcKind::new(Kind::Function(l, r))
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    /// The kind exists in the top context, no parentheses needed.
    Top,
    /// The kind exists in a function argument `Kind -> a`, parentheses are
    /// needed if the kind is a function `(b -> c) -> a`.
    Function,
}

struct DisplayKind<'a>(Prec, &'a Kind);

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", DisplayKind(Prec::Top, self))
    }
}

impl<'a, A, B, E> ToDoc<'a, A, B, E> for ArcKind {
    fn to_doc(&'a self, allocator: &'a A, _: E) -> DocBuilder<'a, A, B>
    where
        A: DocAllocator<'a, B>,
    {
        allocator.text(self.to_string())
    }
}

impl<'a> fmt::Display for DisplayKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self.1 {
            Kind::Hole => "_".fmt(f),
            Kind::Error => "!".fmt(f),
            Kind::Variable(i) => i.fmt(f),
            Kind::Type => "Type".fmt(f),
            Kind::Row => "Row".fmt(f),
            Kind::Function(ref arg, ref ret) => match self.0 {
                Prec::Function => write!(f, "({} -> {})", DisplayKind(Prec::Function, arg), ret),
                Prec::Top => write!(f, "{} -> {}", DisplayKind(Prec::Function, arg), ret),
            },
        }
    }
}

/// Reference counted kind type.
#[derive(Clone, Default, Eq, PartialEq, Hash)]
pub struct ArcKind(Arc<Kind>);

#[cfg(feature = "serde")]
impl<'de, S> crate::serde::de::DeserializeState<'de, S> for ArcKind
where
    S: AsMut<crate::serialization::NodeMap>,
{
    fn deserialize_state<D>(seed: &mut S, deserializer: D) -> Result<ArcKind, D::Error>
    where
        D: crate::serde::Deserializer<'de>,
    {
        use crate::serde::de::DeserializeSeed;
        crate::serialization::SharedSeed::new(seed)
            .deserialize(deserializer)
            .map(ArcKind)
    }
}

impl ArcKind {
    pub fn new(kind: Kind) -> ArcKind {
        ArcKind(Arc::new(kind))
    }

    pub fn make_mut(kind: &mut ArcKind) -> &mut Kind {
        Arc::make_mut(&mut kind.0)
    }

    pub fn strong_count(kind: &ArcKind) -> usize {
        Arc::strong_count(&kind.0)
    }
}

impl Deref for ArcKind {
    type Target = Kind;

    fn deref(&self) -> &Kind {
        &self.0
    }
}

impl From<Kind> for ArcKind {
    fn from(kind: Kind) -> ArcKind {
        ArcKind(Arc::new(kind))
    }
}

impl fmt::Debug for ArcKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for ArcKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

type_cache! { KindCache() () { ArcKind, Kind } row hole error typ }

impl<'a, F: ?Sized> Walker<'a, ArcKind> for F
where
    F: FnMut(&ArcKind),
{
    fn walk(&mut self, typ: &'a ArcKind) {
        self(typ);
        walk_kind(typ, self)
    }
}

pub fn walk_kind<'a, F: ?Sized>(k: &'a ArcKind, f: &mut F)
where
    F: Walker<'a, ArcKind>,
{
    match **k {
        Kind::Function(ref a, ref r) => {
            f.walk(a);
            f.walk(r);
        }
        Kind::Hole | Kind::Error | Kind::Variable(_) | Kind::Type | Kind::Row => (),
    }
}
