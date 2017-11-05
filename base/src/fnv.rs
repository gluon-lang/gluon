extern crate fnv;

use std::collections::{HashMap, HashSet};
use std::hash::BuildHasherDefault;

pub use self::fnv::FnvHasher;

/// Non-crypto `HashMap` using Fnv Hasher
///
/// The default hashing implementation in `std::collections` uses `SipHasher`
/// since gluon doesn't need the cryptographic guarantee provided by `SipHasher`,
/// we've opted for the faster fnv hash.
pub type FnvMap<K, V> = HashMap<K, V, BuildHasherDefault<FnvHasher>>;

/// Non-crypto `HashSet` using Fnv Hasher
///
/// The default hashing implementation in `std::collections` uses `SipHasher`
/// since gluon doesn't need the cryptographic guarantee provided by `SipHasher`,
/// we've opted for the faster fnv hash.
pub type FnvSet<K> = HashSet<K, BuildHasherDefault<FnvHasher>>;
