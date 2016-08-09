extern crate fnv;

use std::collections::HashMap;
use std::hash::BuildHasherDefault;

pub use self::fnv::FnvHasher;

pub type FnvMap<K, V> = HashMap<K, V, BuildHasherDefault<FnvHasher>>;
