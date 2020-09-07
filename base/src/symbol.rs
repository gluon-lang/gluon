//! Module which contains types working with symbols
use std::{
    borrow::Borrow,
    cmp::Ordering,
    convert::TryFrom,
    fmt,
    hash::{BuildHasher, BuildHasherDefault, Hash, Hasher},
    ops::Deref,
    sync::Arc,
};

use crate::{
    ast::{DisplayEnv, IdentEnv},
    pos::{BytePos, Span},
};

// FIXME Don't have a double indirection (Arc + String)
/// A symbol uniquely identifies something regardless of its name and which module it originated
/// from
#[derive(Clone, Eq, Default)]
pub struct Symbol(Arc<SymbolInner>);

#[derive(Debug, Default, Eq, PartialEq, Hash)]
struct SymbolInner {
    global: bool,
    location: Option<u32>,
    name: NameBuf,
}

#[derive(Debug, Default, Eq, PartialEq, Hash)]
pub struct SymbolData<N = NameBuf> {
    pub global: bool,
    pub location: Option<(u32, u32)>,
    pub name: N,
}

#[cfg(feature = "serde")]
mod serialization {
    use super::*;

    use crate::serde::de::DeserializeState;
    use crate::serde::ser::SerializeState;
    use crate::serde::{Deserialize, Deserializer, Serialize, Serializer};
    use crate::serialization::SeSeed;

    impl<'de> Deserialize<'de> for Symbol {
        fn deserialize<D>(deserializer: D) -> Result<Symbol, D::Error>
        where
            D: Deserializer<'de>,
        {
            use std::borrow::Cow;
            Cow::<str>::deserialize(deserializer).map(|s| Symbol::from(&s[..]))
        }
    }

    impl<'de, Id, T> DeserializeState<'de, crate::serialization::Seed<Id, T>> for Symbol {
        fn deserialize_state<D>(
            seed: &mut crate::serialization::Seed<Id, T>,
            deserializer: D,
        ) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            use crate::serde::de::DeserializeSeed;
            use crate::serialization::SharedSeed;

            let seed = SharedSeed::new(seed);
            seed.deserialize(deserializer)
                .map(|s: String| Symbol::from(&s[..]))
        }
    }

    impl Serialize for Symbol {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.collect_str(self)
        }
    }

    impl SerializeState<SeSeed> for Symbol {
        fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            {
                crate::serialization::shared::serialize(self, serializer, seed)
            }
        }
    }
}

impl Deref for Symbol {
    type Target = SymbolRef;
    fn deref(&self) -> &SymbolRef {
        unsafe { &*(&*self.0.name.0 as *const str as *const SymbolRef) }
    }
}

impl Borrow<SymbolRef> for Symbol {
    fn borrow(&self) -> &SymbolRef {
        &**self
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_pretty_str()
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &**self)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_pretty_str())
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        **self == **other
    }
}

impl PartialEq<SymbolRef> for Symbol {
    fn eq(&self, other: &SymbolRef) -> bool {
        **self == *other
    }
}

impl PartialEq<Symbol> for SymbolRef {
    fn eq(&self, other: &Symbol) -> bool {
        *self == **other
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Symbol) -> Option<Ordering> {
        (**self).partial_cmp(other)
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Symbol) -> Ordering {
        (**self).cmp(other)
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}

impl From<String> for Symbol {
    fn from(name: String) -> Symbol {
        Symbol::from(&*name)
    }
}

impl From<(Symbol, Span<BytePos>)> for Symbol {
    fn from((name, _): (Symbol, Span<BytePos>)) -> Symbol {
        name
    }
}

impl<N> From<SymbolData<N>> for Symbol
where
    N: Into<NameBuf>,
{
    fn from(name: SymbolData<N>) -> Symbol {
        Symbol(Arc::new(SymbolInner::new(name)))
    }
}

impl From<&'_ str> for Symbol {
    fn from(name: &str) -> Symbol {
        Symbol(Arc::new(SymbolInner::new(SymbolData::<NameBuf>::from(
            name,
        ))))
    }
}

impl<'a, N> From<&'a str> for SymbolData<N>
where
    N: From<&'a str>,
{
    fn from(mut name: &'a str) -> SymbolData<N> {
        let global = name.starts_with('@');
        let location = match name
            .bytes()
            .rposition(|b| (b < b'0' || b > b'9') && b != b'_')
        {
            Some(i) if i != 0 && name.as_bytes()[i] == b'@' => {
                let loc = &name[(i + 1)..];
                let mut iter = loc.split('_');
                let line = iter.next();
                let col = iter.next();
                let opt = line
                    .and_then(|line| line.parse::<u32>().ok())
                    .and_then(|line| {
                        col.and_then(|col| col.parse::<u32>().ok())
                            .map(|col| (line, col))
                    });

                name = &name[..i];

                opt
            }
            _ => None,
        };

        if global {
            name = &name[1..];
        }

        SymbolData {
            global,
            location,
            name: name.into(),
        }
    }
}

#[derive(Eq)]
#[cfg_attr(feature = "serde_derive", derive(SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct SymbolRef(str);

impl fmt::Debug for SymbolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:p}:{}", self, &self.0)
    }
}

impl fmt::Display for SymbolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &SymbolRef) -> bool {
        self.ptr() == other.ptr()
    }
}

impl PartialOrd for SymbolRef {
    fn partial_cmp(&self, other: &SymbolRef) -> Option<Ordering> {
        self.ptr().partial_cmp(&other.ptr())
    }
}

impl Ord for SymbolRef {
    fn cmp(&self, other: &SymbolRef) -> Ordering {
        self.ptr().cmp(&other.ptr())
    }
}

impl Hash for SymbolRef {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.ptr().hash(h)
    }
}

impl Symbol {
    pub fn strong_count(sym: &Symbol) -> usize {
        Arc::strong_count(&sym.0)
    }

    pub fn is_global(&self) -> bool {
        self.0.global
    }

    pub fn is_primitive(&self) -> bool {
        self.0.name.0.starts_with('#')
    }

    pub fn name_eq(&self, other: &Symbol) -> bool {
        self.name() == other.name()
    }

    pub fn name(&self) -> &Name {
        Name::new(self.as_pretty_str())
    }

    pub fn as_pretty_str(&self) -> &str {
        &self.0.name.0[self.0.global as usize
            ..self
                .0
                .location
                .map_or_else(|| self.0.name.len(), |l| l as usize)]
    }

    pub fn as_data(&self) -> SymbolData<&Name> {
        SymbolData::from(&self.0.name.0[..])
    }
}

impl SymbolRef {
    #[inline]
    pub fn new<N: ?Sized + AsRef<str>>(n: &N) -> &SymbolRef {
        unsafe { &*(Name::new(n) as *const Name as *const SymbolRef) }
    }

    /// Checks whether the names of two symbols are equal
    pub fn name_eq(&self, other: &SymbolRef) -> bool {
        self.name() == other.name()
    }

    pub fn is_global(&self) -> bool {
        self.0.as_bytes().first() == Some(&b'@')
    }

    pub fn as_pretty_str(&self) -> &str {
        let mut s = &self.0;
        if let Some(b'@') = s.as_bytes().first() {
            s = &s[1..];
        }
        Name::new(s).as_pretty_str()
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn name(&self) -> &Name {
        Name::new(Name::new(&self.0).as_pretty_str())
    }

    pub fn raw_name(&self) -> &Name {
        Name::new(&self.0)
    }

    /// Returns the name of this symbol as it was originally declared (strips location information
    /// and module information)
    pub fn declared_name(&self) -> &str {
        self.name().declared_name()
    }

    pub fn definition_name(&self) -> &str {
        Name::new(&self.0).definition_name()
    }

    fn ptr(&self) -> *const () {
        self.0.as_bytes().as_ptr() as *const ()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "S"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "S"))]
pub struct NameBuf(String);

#[derive(Debug, Eq, Hash, Ord, PartialOrd)]
pub struct Name(str);

impl PartialEq for Name {
    fn eq(&self, other: &Name) -> bool {
        self.0.as_ptr() == other.0.as_ptr() || self.0 == other.0
    }
}

impl ToOwned for Name {
    type Owned = NameBuf;

    fn to_owned(&self) -> NameBuf {
        NameBuf::from(self)
    }
}

pub struct Components<'a>(&'a str);

impl<'a> Iterator for Components<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if self.0.is_empty() {
            None
        } else {
            Some(match self.0.find('.') {
                Some(i) => {
                    let (before, after) = self.0.split_at(i);
                    self.0 = &after[1..];
                    before
                }
                None => {
                    let s = self.0;
                    self.0 = "";
                    s
                }
            })
        }
    }
}

impl<'a> From<&'a str> for &'a Name {
    fn from(s: &'a str) -> &'a Name {
        Name::new(s)
    }
}

impl Name {
    #[inline]
    pub fn new<N: ?Sized + AsRef<str>>(n: &N) -> &Name {
        unsafe { &*(n.as_ref() as *const str as *const Name) }
    }

    pub fn as_pretty_str(&self) -> &str {
        Self::strip_position_suffix(&self.0)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn components(&self) -> Components {
        Components(&self.0)
    }

    pub fn module(&self) -> &Name {
        let s = self.0.trim_end_matches(|c| c != '.');
        Name::new(s.trim_end_matches('.'))
    }

    pub fn name(&self) -> &Name {
        self.0
            .rfind('.')
            .map_or(self, |i| Name::new(&self.0[i + 1..]))
    }

    pub fn declared_name(&self) -> &str {
        let name = self.definition_name();
        name.rsplit('.').next().unwrap_or(name)
    }

    pub fn definition_name(&self) -> &str {
        Self::strip_position_suffix(if self.0.as_bytes().get(0) == Some(&b'@') {
            &self.0[1..]
        } else {
            &self.0
        })
    }

    fn strip_position_suffix(name: &str) -> &str {
        // Strip away a `:1234_56` suffix
        let x = match name
            .bytes()
            .rposition(|b| (b < b'0' || b > b'9') && b != b'_')
        {
            Some(i) if name.as_bytes()[i] == b'@' => &name[..i],
            _ => name,
        };

        x
    }
}

impl NameBuf {
    #[inline]
    pub fn new<T>(name: T) -> NameBuf
    where
        T: Into<String>,
    {
        NameBuf(name.into())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl fmt::Display for NameBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Name> for str {
    fn as_ref(&self) -> &Name {
        Name::new(self)
    }
}
impl AsRef<Name> for String {
    fn as_ref(&self) -> &Name {
        Name::new(self)
    }
}
impl AsRef<Name> for Name {
    fn as_ref(&self) -> &Name {
        self
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for NameBuf {
    fn as_ref(&self) -> &str {
        &*self.0
    }
}

impl AsRef<Name> for NameBuf {
    fn as_ref(&self) -> &Name {
        self
    }
}

impl Borrow<Name> for NameBuf {
    fn borrow(&self) -> &Name {
        self
    }
}

impl Deref for NameBuf {
    type Target = Name;
    fn deref(&self) -> &Name {
        Name::new(self)
    }
}

impl<'a> From<&'a str> for NameBuf {
    fn from(name: &'a str) -> NameBuf {
        NameBuf(String::from(name))
    }
}

impl From<String> for NameBuf {
    fn from(name: String) -> NameBuf {
        NameBuf(name)
    }
}

impl From<NameBuf> for String {
    fn from(name: NameBuf) -> String {
        name.0
    }
}

impl<'a> From<&'a Name> for NameBuf {
    fn from(name: &'a Name) -> NameBuf {
        NameBuf::from(&name.0)
    }
}

impl SymbolInner {
    fn new<N>(data: SymbolData<N>) -> SymbolInner
    where
        N: Into<NameBuf>,
    {
        let SymbolData {
            global,
            location,
            name,
        } = data;
        let mut name: NameBuf = name.into();
        if global {
            name.0.insert(0, '@');
        }
        let inner_location = location.map(|(x, y)| {
            let loc = u32::try_from(name.len()).unwrap();
            use std::fmt::Write;
            write!(name.0, "@{}_{}", x, y).unwrap();
            loc
        });

        SymbolInner {
            global,
            location: inner_location,
            name,
        }
    }
}

/// `Symbols` is a bidirectional mapping between `Symbol`s and their name as represented in a
/// source file.
/// Used to make identifiers within a single module point to the same symbol
#[derive(Debug, Default)]
pub struct Symbols {
    indexes:
        hashbrown::HashMap<SymbolData<&'static Name>, Symbol, BuildHasherDefault<fnv::FnvHasher>>,
}

impl Symbols {
    pub fn new() -> Symbols {
        Symbols {
            indexes: Default::default(),
        }
    }

    pub fn simple_symbol<N>(&mut self, name: N) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        self.symbol(SymbolData {
            global: false,
            location: None,
            name,
        })
    }

    /// Looks up the symbol for `name` or creates a new symbol if it does not exist
    pub fn symbol<N>(&mut self, name: SymbolData<N>) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        let name_ref = SymbolData {
            global: name.global,
            location: name.location,
            name: name.name.as_ref(),
        };

        let mut hasher = self.indexes.hasher().build_hasher();
        name_ref.hash(&mut hasher);
        let hash = hasher.finish();

        match self
            .indexes
            .raw_entry_mut()
            .from_hash(hash, |key| *key == name_ref)
        {
            hashbrown::hash_map::RawEntryMut::Occupied(entry) => entry.get().clone(),
            hashbrown::hash_map::RawEntryMut::Vacant(entry) => {
                let SymbolData {
                    global,
                    location,
                    name,
                } = name;
                let mut name: NameBuf = name.into();
                if global {
                    name.0.insert(0, '@');
                }
                let inner_location = location.map(|(x, y)| {
                    let loc = u32::try_from(name.len()).unwrap();
                    use std::fmt::Write;
                    write!(name.0, "@{}_{}", x, y).unwrap();
                    loc
                });

                let key = unsafe { &*(name.definition_name() as *const str as *const Name) };
                let s = Symbol(Arc::new(SymbolInner {
                    global,
                    location: inner_location,
                    name,
                }));
                entry
                    .insert_hashed_nocheck(
                        hash,
                        SymbolData {
                            global,
                            location,
                            name: key,
                        },
                        s,
                    )
                    .1
                    .clone()
            }
        }
    }

    pub fn contains_name<N>(&mut self, name: N) -> bool
    where
        N: AsRef<Name>,
    {
        let s = SymbolData::<&Name>::from(name.as_ref().as_str());
        self.indexes.contains_key(&s)
    }

    pub fn len(&self) -> usize {
        self.indexes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.indexes.is_empty()
    }
}

/// `SymbolModule` wraps a `Symbols` struct and adds a prefix to all symbols created by the
/// `symbol` method.
/// While this prefix does not affect the uniques of a `Symbol` in any way, it does make the origin
/// of a symbol clearer when pretty printing it
#[derive(Debug)]
pub struct SymbolModule<'a> {
    symbols: &'a mut Symbols,
    module: NameBuf,
}

impl<'a> SymbolModule<'a> {
    pub fn new(module: String, symbols: &'a mut Symbols) -> SymbolModule<'a> {
        SymbolModule {
            symbols,
            module: NameBuf(module),
        }
    }

    pub fn simple_symbol<N>(&mut self, name: N) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        self.symbols.simple_symbol(name)
    }

    /// Creates an unprefixed symbol, same as `Symbols::symbol`
    pub fn symbol<N>(&mut self, name: SymbolData<N>) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        self.symbols.symbol(name)
    }

    pub fn contains_name<N>(&mut self, name: N) -> bool
    where
        N: AsRef<Name>,
    {
        self.symbols.contains_name(name.as_ref())
    }

    /// Creates a symbol which is prefixed by the `module` argument passed in `new`
    ///
    /// ```
    /// # use gluon_base::symbol::{Symbols, SymbolModule};
    /// let mut symbols = Symbols::new();
    /// let mut symbols = SymbolModule::new(String::from("test"), &mut symbols);
    /// assert_eq!(symbols.simple_symbol("a").as_ref(), "a");
    /// assert_eq!(symbols.scoped_symbol("a").as_ref(), "test.a");
    /// ```
    pub fn scoped_symbol(&mut self, name: &str) -> Symbol {
        let len = self.module.0.len();
        self.module.0.push('.');
        self.module.0.push_str(name);
        let symbol = self.symbols.symbol(SymbolData {
            global: false,
            location: None,
            name: &*self.module,
        });
        self.module.0.truncate(len);
        symbol
    }

    pub fn module(&self) -> &Name {
        &self.module
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    pub fn symbols(&mut self) -> &mut Symbols {
        self.symbols
    }
}

impl DisplayEnv for Symbols {
    type Ident = Symbol;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl IdentEnv for Symbols {
    fn from_str(&mut self, s: &str) -> Symbol {
        self.symbol(SymbolData::<&Name>::from(s))
    }
}

impl<'s> DisplayEnv for SymbolModule<'s> {
    type Ident = Symbol;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.symbols.string(ident)
    }
}

impl<'a> IdentEnv for SymbolModule<'a> {
    fn from_str(&mut self, s: &str) -> Symbol {
        self.symbol(SymbolData::<&Name>::from(s))
    }
}

impl<P> From<crate::pos::Spanned<Symbol, P>> for Symbol {
    fn from(s: crate::pos::Spanned<Symbol, P>) -> Self {
        s.value
    }
}
