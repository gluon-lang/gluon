use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use symbol::SymbolRef;
use types::Walker;

/// Trait for values which contains kinded values which can be refered by name
pub trait KindEnv {
    /// Returns the kind of the type `type_name`
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind>;
}

impl<'a, T: ?Sized + KindEnv> KindEnv for &'a T {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        (**self).find_kind(id)
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
pub enum Kind {
    /// Representation for a kind which is yet to be inferred.
    Variable(u32),
    /// The simplest possible kind. All values in a program have this kind.
    Type,
    /// Kinds of rows (for polymorphic records).
    Row,
    /// Constructor which takes two kinds, taking the first as argument and returning the second.
    Function(ArcKind, ArcKind),
}

impl Kind {
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

impl<'a> fmt::Display for DisplayKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self.1 {
            Kind::Variable(i) => i.fmt(f),
            Kind::Type => "Type".fmt(f),
            Kind::Row => "Row".fmt(f),
            Kind::Function(ref arg, ref ret) => {
                match self.0 {
                    Prec::Function => {
                        write!(f, "({} -> {})", DisplayKind(Prec::Function, arg), ret)
                    }
                    Prec::Top => write!(f, "{} -> {}", DisplayKind(Prec::Function, arg), ret),
                }
            }
        }
    }
}

/// Reference counted kind type.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ArcKind(Arc<Kind>);

impl Deref for ArcKind {
    type Target = Kind;

    fn deref(&self) -> &Kind {
        &self.0
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

impl ArcKind {
    pub fn new(k: Kind) -> ArcKind {
        ArcKind(Arc::new(k))
    }
}

impl<F: ?Sized> Walker<ArcKind> for F
    where F: FnMut(&ArcKind),
{
    fn walk(&mut self, typ: &ArcKind) {
        self(typ);
        walk_kind(typ, self)
    }
}

pub fn walk_kind<F: ?Sized>(k: &ArcKind, f: &mut F)
    where F: Walker<ArcKind>,
{
    match **k {
        Kind::Function(ref a, ref r) => {
            f.walk(a);
            f.walk(r);
        }
        Kind::Variable(_) |
        Kind::Type |
        Kind::Row => (),
    }
}
