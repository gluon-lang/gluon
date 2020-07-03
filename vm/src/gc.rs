use std::{
    any::{Any, TypeId},
    cell::Cell,
    cmp::Ordering,
    collections::{hash_map::Entry, HashMap, HashSet, VecDeque},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    rc::Rc,
    result::Result as StdResult,
    sync::{self, Arc},
};

use crate::{
    base::fnv::FnvMap, forget_lifetime, interner::InternedStr, types::VmIndex, Error, Result,
};

pub mod mutex;

#[doc(hidden)]
#[macro_export]
macro_rules! impl_trace {
    ($self_: tt, $gc: ident, $body: expr) => {
        unsafe fn root(&mut $self_) {
            #[allow(unused)]
            unsafe fn mark<T: ?Sized + Trace>(this: &mut T, _: ()) {
                Trace::root(this)
            }
            let $gc = ();
            $body
        }
        unsafe fn unroot(&mut $self_) {
            #[allow(unused)]
            unsafe fn mark<T: ?Sized + Trace>(this: &mut T, _: ()) {
                Trace::unroot(this)
            }
            let $gc = ();
            $body
        }
        fn trace(&$self_, $gc: &mut $crate::gc::Gc) {
            #[allow(unused)]
            fn mark<T: ?Sized + Trace>(this: &T, gc: &mut $crate::gc::Gc) {
                Trace::trace(this, gc)
            }
            $body
        }
    }
}

macro_rules! deref_trace_mut {
    ([$($params: tt)*] $ty: ty) => {
        unsafe impl<$($params)*> Trace for $ty {
            unsafe fn root(&mut self) {
                (**self).root();
            }
            unsafe fn unroot(&mut self) {
                (**self).unroot();
            }
            fn trace(&self, gc: &mut Gc) {
                (**self).trace(gc);
            }
        }
    };
}

macro_rules! deref_trace {
    ([$($params: tt)*] $ty: ty) => {
        unsafe impl<$($params)*> Trace for $ty {
            fn trace(&self, gc: &mut Gc) {
                (**self).trace(gc);
            }
        }
    };
}

macro_rules! impl_trace_fields {
    ($self_: tt, $gc: ident;  $($field: ident),*) => {
        impl_trace!{ $self_, $gc,
            match $self_ {
                Self { $($field,)* .. } => {
                    $(
                        mark($field, $gc);
                    )*
                }
            }
        }
    }
}

#[inline]
unsafe fn allocate(size: usize) -> *mut u8 {
    // Allocate an extra element if it does not fit exactly
    let cap = size / mem::size_of::<f64>()
        + (if size % mem::size_of::<f64>() != 0 {
            1
        } else {
            0
        });
    ptr_from_vec(Vec::<f64>::with_capacity(cap))
}

#[inline]
fn ptr_from_vec(mut buf: Vec<f64>) -> *mut u8 {
    let ptr = buf.as_mut_ptr();
    mem::forget(buf);

    ptr as *mut u8
}

#[inline]
unsafe fn deallocate(ptr: *mut u8, old_size: usize) {
    let cap = old_size / mem::size_of::<f64>()
        + (if old_size % mem::size_of::<f64>() != 0 {
            1
        } else {
            0
        });
    Vec::<f64>::from_raw_parts(ptr as *mut f64, 0, cap);
}

/// Pointer type which can only be written to.
pub struct WriteOnly<'s, T: ?Sized + 's>(*mut T, PhantomData<&'s mut T>);

impl<'s, T: ?Sized> WriteOnly<'s, T> {
    /// Unsafe as the lifetime must not be longer than the liftime of `t`
    pub unsafe fn new(t: *mut T) -> WriteOnly<'s, T> {
        WriteOnly(t, PhantomData)
    }

    /// Retrieves the pointer allowing it to be manipulated freely.
    /// As it points to uninitialized data care must be taken so to not read it before it has been
    /// initialized
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.0
    }
}

impl<'s, T> WriteOnly<'s, T> {
    /// Writes a value to the pointer and returns a pointer to the now initialized value.
    pub fn write(self, t: T) -> &'s mut T {
        unsafe {
            ptr::write(self.0, t);
            &mut *self.0
        }
    }
}

impl<'s, T: Copy> WriteOnly<'s, [T]> {
    pub fn write_slice(self, s: &[T]) -> &'s mut [T] {
        let self_ = unsafe { &mut *self.0 };
        assert!(s.len() == self_.len());
        for (to, from) in self_.iter_mut().zip(s) {
            *to = *from;
        }
        self_
    }
}

impl<'s> WriteOnly<'s, str> {
    pub fn write_str(self, s: &str) -> &'s mut str {
        unsafe {
            let ptr: &mut [u8] = mem::transmute::<*mut str, &mut [u8]>(self.0);
            assert!(s.len() == ptr.len());
            for (to, from) in ptr.iter_mut().zip(s.as_bytes()) {
                *to = *from;
            }
            &mut *self.0
        }
    }
}

#[derive(Clone, Copy, Default, Debug)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub struct Generation(i32);

impl Generation {
    pub fn is_root(self) -> bool {
        self.0 == 0
    }

    /// Returns a generation which compared to any normal generation is always younger.
    pub fn disjoint() -> Generation {
        Generation(-1)
    }

    /// Returns wheter `self` is a parent of the other generation.
    pub fn is_parent_of(self, other: Generation) -> bool {
        self.0 < other.0
    }

    /// Returns true if `self` can contain a value from generation `other`
    pub fn can_contain_values_from(self, other: Generation) -> bool {
        other.0 <= self.0
    }

    pub fn next(self) -> Generation {
        assert!(
            self.0 < i32::max_value(),
            "To many generations has been created"
        );
        Generation(self.0 + 1)
    }
}

/// A mark and sweep garbage collector.
#[derive(Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct Gc {
    /// Linked list of all objects allocted by this garbage collector.
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    values: Option<AllocPtr>,
    /// How many bytes which is currently allocated
    allocated_memory: usize,
    /// How many bytes this garbage collector can allocate before a collection is run
    collect_limit: usize,
    /// The maximum number of bytes this garbage collector may contain
    memory_limit: usize,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    type_infos: FnvMap<TypeId, Box<TypeInfo>>,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    record_infos: FnvMap<Arc<[InternedStr]>, Box<TypeInfo>>,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    tag_infos: FnvMap<InternedStr, Box<TypeInfo>>,
    /// The generation of a gc determines what values it needs to copy and what values it can
    /// share. A gc can share values generated by itself (the same generation) and those in an
    /// earlier (lower) generation. It is important to note that two garbage collectors can have
    /// the same value as their generation but that does not mean that they can share values. This
    /// is only enforced in that values can only be shared up or down the tree of generations.
    ///
    /// Example:
    ///           0
    ///          / \
    ///         1   1
    ///        /   / \
    ///       2   2   2
    /// Generations 2 can share values with anything above them in the tree so refering to anything
    /// of generation 1 or 0 does not require a copy. Generation 1 can only share values with
    /// generation 0 so if a generation two value is shared up the tree it needs to be cloned.
    ///
    /// Between the generation 2 garbage collectors no values can be directly shared as they could
    /// only refer to each other through some reference or channel allocated in generation 0 (and
    /// if they do interact with eachother this means the values are cloned into generation 0).
    generation: Generation,
}

impl Drop for Gc {
    fn drop(&mut self) {
        if let Some(values) = self.values.take() {
            mem::forget(values);
            if std::thread::panicking() {
                eprintln!("Gc values were not dropped explicitly. Leaking the allocatons!");
            } else {
                panic!("Gc values were not dropped explicitly. Leaking the allocatons!");
            }
        }
    }
}

/// Trait which creates a typed pointer from a *mut () pointer.
/// For `Sized` types this is just a cast but for unsized types some more metadata must be taken
/// from the provided `D` value to make it initialize correctly.
pub unsafe trait FromPtr<D> {
    unsafe fn make_ptr(data: D, ptr: *mut ()) -> *mut Self;
}

unsafe impl<D, T> FromPtr<D> for T {
    unsafe fn make_ptr(_: D, ptr: *mut ()) -> *mut Self {
        ptr as *mut Self
    }
}

unsafe impl<'s, 't, T> FromPtr<&'s &'t [T]> for [T] {
    unsafe fn make_ptr(v: &'s &'t [T], ptr: *mut ()) -> *mut [T] {
        ::std::slice::from_raw_parts_mut(ptr as *mut T, v.len())
    }
}

/// A definition of some data which may be allocated by the garbage collector.
pub unsafe trait DataDef {
    /// The type of the value allocated.
    type Value: ?Sized + for<'a> FromPtr<&'a Self> + Trace;
    /// Returns how many bytes need to be allocted for this `DataDef`
    fn size(&self) -> usize;
    /// Consumes `self` to initialize the allocated value.
    /// Returns the initialized pointer.
    fn initialize<'w>(self, ptr: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value;

    fn fields(&self) -> Option<&[InternedStr]> {
        None
    }

    fn tag(&self) -> Option<&InternedStr> {
        None
    }
}

/// `DataDef` that moves its value directly into the pointer
/// useful for sized types
#[derive(Trace)]
#[gluon(gluon_vm)]
pub struct Move<T>(pub T);

unsafe impl<T> DataDef for Move<T>
where
    T: Trace,
{
    type Value = T;
    fn size(&self) -> usize {
        mem::size_of::<T>()
    }
    fn initialize(self, result: WriteOnly<T>) -> &mut T {
        result.write(self.0)
    }
}

#[derive(Debug)]
struct TypeInfo {
    drop: unsafe fn(*mut ()),
    generation: Generation,
    tag: Option<InternedStr>,
    fields: FnvMap<InternedStr, VmIndex>,
    fields_key: Arc<[InternedStr]>,
}

#[derive(Debug)]
struct GcHeader {
    next: Option<AllocPtr>,
    marked: Cell<bool>,
    value_size: usize,
    type_info: *const TypeInfo,
}

struct AllocPtr {
    ptr: *mut GcHeader,
}

unsafe impl Send for AllocPtr {}

impl AllocPtr {
    fn new<T>(type_info: *const TypeInfo, value_size: usize) -> AllocPtr {
        fn new(type_info: *const TypeInfo, value_size: usize) -> AllocPtr {
            unsafe {
                let alloc_size = GcHeader::value_offset() + value_size;
                let ptr = allocate(alloc_size) as *mut GcHeader;
                ptr::write(
                    ptr,
                    GcHeader {
                        next: None,
                        type_info: type_info,
                        value_size: value_size,
                        marked: Cell::new(false),
                    },
                );
                AllocPtr { ptr }
            }
        }
        debug_assert!(mem::align_of::<T>() <= mem::align_of::<f64>());
        new(type_info, value_size)
    }

    fn size(&self) -> usize {
        GcHeader::value_offset() + self.value_size
    }
}

impl fmt::Debug for AllocPtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AllocPtr {{ ptr: {:?} }}", &**self)
    }
}

impl Drop for AllocPtr {
    fn drop(&mut self) {
        unsafe {
            // Avoid stack overflow by looping through all next pointers instead of doing it
            // recursively
            let mut current = self.next.take();
            while let Some(mut next) = current {
                current = next.next.take();
            }
            let size = self.size();
            ((*self.type_info).drop)(self.value());
            ptr::read(&*self.ptr);
            deallocate(self.ptr as *mut u8, size);
        }
    }
}

impl Deref for AllocPtr {
    type Target = GcHeader;
    fn deref(&self) -> &GcHeader {
        unsafe { &*self.ptr }
    }
}

impl DerefMut for AllocPtr {
    fn deref_mut(&mut self) -> &mut GcHeader {
        unsafe { &mut *self.ptr }
    }
}

impl GcHeader {
    fn value(&mut self) -> *mut () {
        unsafe {
            let ptr: *mut GcHeader = self;
            (ptr as *mut u8).offset(GcHeader::value_offset() as isize) as *mut ()
        }
    }

    fn value_offset() -> usize {
        let hs = mem::size_of::<GcHeader>();
        let max_align = mem::align_of::<f64>();
        hs + ((max_align - (hs % max_align)) % max_align)
    }

    fn generation(&self) -> Generation {
        unsafe { (*self.type_info).generation }
    }
}

pub struct OwnedPtr<T: ?Sized>(NonNull<T>);

impl<T: ?Sized> Deref for OwnedPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }
}

impl<T: ?Sized> DerefMut for OwnedPtr<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut() }
    }
}

impl<T: ?Sized> From<OwnedPtr<T>> for GcPtr<T> {
    /// Freezes `self` into a shared pointer
    fn from(ptr: OwnedPtr<T>) -> GcPtr<T> {
        GcPtr(ptr.0)
    }
}

/// SAFETY The only unsafety from copying the type is the creation of an unrooted value
pub unsafe trait CopyUnrooted: CloneUnrooted<Value = Self> + Sized {
    unsafe fn copy_unrooted(&self) -> Self {
        ptr::read(self)
    }
}

pub trait CloneUnrooted {
    type Value;
    /// Creates a clone of the value that is not rooted. To ensure safety the value must be
    /// forgotten or rooted before the next garbage collection
    unsafe fn clone_unrooted(&self) -> Self::Value;
}

impl<T: ?Sized + CloneUnrooted> CloneUnrooted for &'_ T {
    type Value = T::Value;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self::Value {
        (**self).clone_unrooted()
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Borrow<'a, T>(T, PhantomData<&'a T>);

pub type GcRef<'a, T> = Borrow<'a, GcPtr<T>>;
pub type OwnedGcRef<'a, T> = Borrow<'a, OwnedPtr<T>>;

impl<T> Deref for Borrow<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> DerefMut for Borrow<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> CloneUnrooted for Borrow<'_, T>
where
    T: CloneUnrooted,
{
    type Value = T::Value;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self::Value {
        self.0.clone_unrooted()
    }
}

deref_trace! { ['a, T: Trace] Borrow<'a, T> }

unsafe impl<'a, T> DataDef for Borrow<'a, T>
where
    T: DataDef,
    T::Value: Sized,
{
    type Value = T::Value;
    fn size(&self) -> usize {
        (**self).size()
    }
    fn initialize(self, result: WriteOnly<Self::Value>) -> &mut Self::Value {
        self.0.initialize(result)
    }
}

impl<'gc, T> Borrow<'gc, T> {
    #[inline]
    pub fn new(value: &'gc T) -> Borrow<'gc, T::Value>
    where
        T: CloneUnrooted,
    {
        // SAFETY The returned value is tied to the lifetime of the `value` root meaning the
        // GcRef is also rooted
        unsafe { Borrow::with_root(value.clone_unrooted(), value) }
    }

    #[inline]
    pub fn from_static(value: T) -> Self
    where
        T: 'static, // TODO Necessary?
    {
        Borrow(value, PhantomData)
    }

    #[inline]
    pub(crate) unsafe fn with_root<U: ?Sized>(value: T, _root: &'gc U) -> Self {
        Borrow(value, PhantomData)
    }

    pub fn map<U>(&self, f: impl FnOnce(&T) -> &U) -> Borrow<'gc, U::Value>
    where
        U: CloneUnrooted,
    {
        let v = f(&self.0);
        // SAFETY We can create a new root since the `'gc` lifetime is preserved
        unsafe { Borrow(v.clone_unrooted(), PhantomData) }
    }

    pub unsafe fn map_unrooted<U>(self, f: impl FnOnce(T) -> U) -> Borrow<'gc, U> {
        Borrow(f(self.0), PhantomData)
    }

    pub unsafe fn unrooted(self) -> T {
        self.0
    }

    pub fn as_lifetime(&self) -> &'gc () {
        &()
    }
}

impl<'gc, T: ?Sized> From<OwnedGcRef<'gc, T>> for GcRef<'gc, T> {
    /// Freezes `self` into a shared pointer
    fn from(ptr: OwnedGcRef<'gc, T>) -> Self {
        Borrow(ptr.0.into(), PhantomData)
    }
}

impl<'a, T: ?Sized> Clone for GcRef<'a, T> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY The lifetime of the new value is the same which just means that both values need
        // to be dropped before any gc collection
        unsafe { Borrow(self.0.clone_unrooted(), self.1) }
    }
}

impl<'a, T: ?Sized> GcRef<'a, T> {
    pub fn as_ref(&self) -> &'a T {
        // SAFETY 'a is the lifetime that the value actually lives. Since `T` is behind a pointer
        // we can make that pointer have that lifetime
        unsafe { forget_lifetime(&*self.0) }
    }
}

/// A pointer to a garbage collected value.
///
/// It is only safe to access data through a `GcPtr` if the value is rooted (stored in a place
/// where the garbage collector will find it during the mark phase).
pub struct GcPtr<T: ?Sized>(NonNull<T>);

// SAFETY Copied from `Arc`
unsafe impl<T: ?Sized + Send + Sync> Send for GcPtr<T> {}
unsafe impl<T: ?Sized + Send + Sync> Sync for GcPtr<T> {}

impl<T: ?Sized> Deref for GcPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }
}

impl<T: ?Sized> ::std::borrow::Borrow<T> for GcPtr<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized + Eq> Eq for GcPtr<T> {}
impl<T: ?Sized + PartialEq> PartialEq for GcPtr<T> {
    fn eq(&self, other: &GcPtr<T>) -> bool {
        **self == **other
    }
}

impl<T: ?Sized + Ord> Ord for GcPtr<T> {
    fn cmp(&self, other: &GcPtr<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}
impl<T: ?Sized + PartialOrd> PartialOrd for GcPtr<T> {
    fn partial_cmp(&self, other: &GcPtr<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Hash> Hash for GcPtr<T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (**self).hash(state)
    }
}
impl<T: ?Sized + fmt::Debug> fmt::Debug for GcPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}
impl<T: ?Sized + fmt::Display> fmt::Display for GcPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

unsafe impl<T: ?Sized> CopyUnrooted for GcPtr<T> {}
impl<T: ?Sized> CloneUnrooted for GcPtr<T> {
    type Value = Self;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self {
        GcPtr(self.0)
    }
}

impl<T: ?Sized> GcPtr<T> {
    /// Unsafe as it is up to the caller to ensure that this pointer is not referenced somewhere
    /// else
    pub unsafe fn as_mut(&mut self) -> &mut T {
        self.0.as_mut()
    }

    /// Unsafe as `ptr` must have been allocted by this garbage collector
    pub unsafe fn from_raw(ptr: *const T) -> GcPtr<T> {
        GcPtr(NonNull::new_unchecked(ptr as *mut _))
    }

    pub fn generation(&self) -> Generation {
        self.header().generation()
    }

    pub fn poly_tag(&self) -> Option<&InternedStr> {
        self.type_info().tag.as_ref()
    }

    pub fn field_map(&self) -> &FnvMap<InternedStr, VmIndex> {
        &self.type_info().fields
    }

    pub fn field_names(&self) -> &Arc<[InternedStr]> {
        &self.type_info().fields_key
    }

    fn type_info(&self) -> &TypeInfo {
        unsafe { &*self.header().type_info }
    }

    pub fn ptr_eq(&self, other: &GcPtr<T>) -> bool {
        ptr::eq::<T>(&**self, &**other)
    }

    #[doc(hidden)]
    pub(crate) unsafe fn clone(&self) -> Self {
        GcPtr(self.0)
    }

    pub unsafe fn unrooted(&self) -> Self {
        GcPtr(self.0)
    }

    pub fn as_lifetime(&self) -> &() {
        &()
    }

    fn header(&self) -> &GcHeader {
        unsafe {
            let p = self.0.as_ptr() as *mut u8;
            let header = p.offset(-(GcHeader::value_offset() as isize));
            &*(header as *const GcHeader)
        }
    }

    pub unsafe fn cast<U>(ptr: Self) -> GcPtr<U> {
        GcPtr(ptr.0.cast())
    }
}

impl<'a, T: Trace + Send + Sync + 'a> GcPtr<T> {
    /// Coerces `self` to a `Trace` trait object
    pub fn as_trace(self) -> GcPtr<dyn Trace + Send + Sync + 'a> {
        unsafe {
            let ptr: &(dyn Trace + Send + Sync) = self.0.as_ref();
            GcPtr(NonNull::new_unchecked(ptr as *const _ as *mut _))
        }
    }
}
impl GcPtr<str> {
    /// Coerces `self` to a `Trace` trait object
    pub fn as_trace_string(self) -> GcPtr<dyn Trace + Send + Sync> {
        // As there is nothing to trace in a str we can safely cast it to *const u8 and use
        // u8's Trace impl
        unsafe {
            GcPtr(NonNull::new_unchecked(
                self.as_ptr() as *const (dyn Trace + Send + Sync) as *mut _,
            ))
        }
    }
}

pub trait CollectScope {
    fn scope<F>(&self, gc: &mut Gc, f: F)
    where
        F: FnOnce(&mut Gc);
}

/// Trait which must be implemented on all root types which contain `GcPtr`
/// A type unsafe implementing Trace must call trace on each of its fields
/// which in turn contains `GcPtr`
pub unsafe trait Trace {
    unsafe fn root(&mut self) {}
    unsafe fn unroot(&mut self) {}

    fn trace(&self, gc: &mut Gc) {
        let _ = gc;
    }
}

#[macro_export]
macro_rules! construct_enum_gc {
    (impl $typ: ident $(:: $variant: ident)? [$($acc: tt)*] [$($ptr: ident)*] @ $expr: expr, $($rest: tt)*) => { {
        let ref ptr = $expr;
        $crate::construct_enum_gc!(impl $typ $(:: $variant)?
                      [$($acc)* unsafe { $crate::gc::CloneUnrooted::clone_unrooted(ptr) },]
                      [$($ptr)* ptr]
                      $($rest)*
        )
    } };

    (impl $typ: ident $(:: $variant: ident)? [$($acc: tt)*] [$($ptr: ident)*] $expr: expr, $($rest: tt)*) => {
        $crate::construct_enum_gc!(impl $typ $(:: $variant)?
                      [$($acc)* $expr,]
                      [$($ptr)*]
                      $($rest)*
        )
    };

    (impl $typ: ident $(:: $variant: ident)? [$($acc: tt)*] [$($ptr: ident)*] @ $expr: expr) => { {
        let ref ptr = $expr;
        $crate::construct_enum_gc!(impl $typ $(:: $variant)?
                      [$($acc)* unsafe { $crate::gc::CloneUnrooted::clone_unrooted(ptr) },]
                      [$($ptr)* ptr]
        )
    } };

    (impl $typ: ident $(:: $variant: ident)? [$($acc: tt)*] [$($ptr: ident)*] $expr: expr) => {
        $crate::construct_enum_gc!(impl $typ $(:: $variant)?
                      [$($acc)* $expr,]
                      [$($ptr)*]
        )
    };

    (impl $typ: ident $(:: $variant: ident)? [$($acc: tt)*] [$($ptr: ident)*] ) => { {
        let root = [$( $ptr.as_lifetime() )*].first().map_or(&(), |v| *v);
        #[allow(unused_unsafe)]
        let v = $typ $(:: $variant)? ( $($acc)* );
        // Make sure that we constructed something and didn't call a function which could leak the
        // pointers
        match &v {
            $typ $(:: $variant)? (..) if true => (),
            _ => unreachable!(),
        }
        #[allow(unused_unsafe)]
        unsafe { $crate::gc::Borrow::with_root(v, root) }
    } };
}

#[macro_export]
macro_rules! construct_gc {
    (impl $typ: ident [$($acc: tt)*] [$($ptr: ident)*] @ $field: ident : $expr: expr, $($rest: tt)*) => { {
        let $field = $expr;
        $crate::construct_gc!(impl $typ
                      [$($acc)* $field: unsafe { $crate::gc::CloneUnrooted::clone_unrooted(&$field) },]
                      [$($ptr)* $field]
                      $($rest)*
        )
    } };

    (impl $typ: ident [$($acc: tt)*] [$($ptr: ident)*] @ $field: ident, $($rest: tt)*) => {
        $crate::construct_gc!(impl $typ
                      [$($acc)* $field: unsafe { $crate::gc::CloneUnrooted::clone_unrooted(&$field) },]
                      [$($ptr)* $field]
                      $($rest)*
        )
    };

    (impl $typ: ident [$($acc: tt)*] [$($ptr: ident)*] $field: ident $(: $expr: expr)?, $($rest: tt)*) => {
        $crate::construct_gc!(impl $typ
                      [$($acc)* $field $(: $expr)?,]
                      [$($ptr)*]
                      $($rest)*
        )
    };

    (impl $typ: ident [$($acc: tt)*] [$($ptr: ident)*] ) => { {
        let root = [$( $ptr.as_lifetime() )*].first().map_or(&(), |v| *v);
        #[allow(unused_unsafe)]
        let v = $typ { $($acc)* };
        #[allow(unused_unsafe)]
        unsafe { $crate::gc::Borrow::with_root(v, root) }
    } };

    ($typ: ident { $( $tt: tt )* } ) => {
        $crate::construct_gc!{impl $typ [] [] $( $tt )* }
    };

    ($typ: ident $(:: $variant: ident)? ( $( $tt: tt )* ) ) => {
        $crate::construct_enum_gc!{impl $typ $(:: $variant)? [] [] $( $tt )* }
    };
}

deref_trace! { ['a, T: ?Sized + Trace] &'a T }
deref_trace_mut! { ['a, T: ?Sized + Trace] &'a mut T }
deref_trace_mut! { ['a, T: ?Sized + Trace] Box<T> }
deref_trace! { ['a, T: ?Sized + Trace] Arc<T> }
deref_trace! { ['a, T: ?Sized + Trace] Rc<T> }
deref_trace_mut! { ['a, T: Trace] Vec<T> }

macro_rules! tuple_trace {
    () => {};
    ($first: ident $($id: ident)*) => {
        tuple_trace!($($id)*);
        unsafe impl <$first $(,$id)*> Trace for ($first, $($id,)*)
            where $first: Trace
                  $(, $id: Trace)* {
            impl_trace! { self, gc,{
                #[allow(non_snake_case)]
                let ($first, $($id,)*) = self;
                mark($first, gc);
                $(
                    mark($id, gc);
                )*
            } }
        }
    }
}

tuple_trace!(A B C D E F G H I J);

macro_rules! empty_trace {
    ($($id: ty)*) => {
        $(unsafe impl Trace for $id {
            impl_trace! { self, _gc, {} }
        })*
    }
}

empty_trace! { () u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64 str String bool }

unsafe impl<T> Trace for Option<T>
where
    T: Trace,
{
    impl_trace! { self, gc,
        if let Some(x) = self {
            mark(x, gc);
        }
    }
}

unsafe impl<T, E> Trace for StdResult<T, E>
where
    T: Trace,
    E: Trace,
{
    impl_trace! { self, gc,
        match self {
            Ok(x) => mark(x, gc),
            Err(x) => mark(x, gc),
        }
    }
}

unsafe impl<T: ?Sized> Trace for PhantomData<T> {
    impl_trace! { self, _gc, {} }
}

unsafe impl<T: ?Sized> Trace for *const T {
    impl_trace! { self, _gc, { } }
}

unsafe impl<T: ?Sized> Trace for *mut T {
    impl_trace! { self, _gc, { } }
}

unsafe impl<T> Trace for Cell<T>
where
    T: Trace + Copy,
{
    impl_trace! { self, gc,
        mark(&mut self.get(), gc)
    }
}

// Don't root/unroot the contents as an unrooted value could be moved out of the Mutex
unsafe impl<T> Trace for sync::Mutex<T>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        self.lock().unwrap_or_else(|err| err.into_inner()).trace(gc)
    }
}

// Don't root/unroot the contents as an unrooted value could be moved out of the RwLock
unsafe impl<T> Trace for sync::RwLock<T>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        self.read().unwrap_or_else(|err| err.into_inner()).trace(gc)
    }
}

unsafe impl<T> Trace for sync::RwLockReadGuard<'_, T>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        (&**self).trace(gc)
    }
}

unsafe impl<T> Trace for parking_lot::RwLock<T>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        self.read().trace(gc)
    }
}

unsafe impl<T> Trace for parking_lot::RwLockReadGuard<'_, T>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        (&**self).trace(gc)
    }
}

unsafe impl<U> Trace for [U]
where
    U: Trace,
{
    impl_trace! { self, gc,
        for x in self {
            mark(x, gc);
        }
    }
}

unsafe impl<T> Trace for VecDeque<T>
where
    T: Trace,
{
    impl_trace! { self, gc,
        mark(&mut self.as_slices(), gc)
    }
}

unsafe impl<K, V, H> Trace for HashMap<K, V, H>
where
    V: Trace,
{
    impl_trace! { self, gc,
        for (_, x) in self {
            mark(x, gc);
        }
    }
}

unsafe impl<V, H> Trace for HashSet<V, H>
where
    V: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        for x in self.iter() {
            x.trace(gc);
        }
    }
}

/// When traversing a `GcPtr` we need to mark it
unsafe impl<T: ?Sized> Trace for GcPtr<T>
where
    T: Trace,
{
    unsafe fn root(&mut self) {
        // Anything inside a `GcPtr` is implicitly rooted by the pointer itself being rooted
    }
    unsafe fn unroot(&mut self) {
        // Anything inside a `GcPtr` is implicitly rooted by the pointer itself being rooted
    }
    fn trace(&self, gc: &mut Gc) {
        if !gc.mark(self) {
            // Continue traversing if this ptr was not already marked
            (**self).trace(gc);
        }
    }
}

impl Gc {
    /// Constructs a new garbage collector
    pub fn new(generation: Generation, memory_limit: usize) -> Gc {
        Gc {
            values: None,
            allocated_memory: 0,
            collect_limit: 100,
            memory_limit: memory_limit,
            type_infos: FnvMap::default(),
            record_infos: FnvMap::default(),
            tag_infos: FnvMap::default(),
            generation: generation,
        }
    }

    pub fn allocated_memory(&self) -> usize {
        self.allocated_memory
    }

    pub fn set_memory_limit(&mut self, memory_limit: usize) {
        self.memory_limit = memory_limit;
    }

    pub fn generation(&self) -> Generation {
        self.generation
    }

    pub fn new_child_gc(&self) -> Gc {
        Gc::new(self.generation.next(), self.memory_limit)
    }

    /// Allocates a new object. If the garbage collector has hit the collection limit a collection
    /// will occur.
    ///
    /// Unsafe since `roots` must be able to trace all accesible `GcPtr` values.
    pub unsafe fn alloc_and_collect<R, D>(
        &mut self,
        roots: R,
        def: D,
    ) -> Result<OwnedGcRef<D::Value>>
    where
        R: Trace + CollectScope,
        D: DataDef + Trace,
        D::Value: Sized + Any,
    {
        #[derive(Trace)]
        #[gluon(gluon_vm)]
        struct Scope1<A, B>(A, B);

        impl<A, B> CollectScope for Scope1<A, B>
        where
            A: CollectScope,
        {
            fn scope<F>(&self, gc: &mut Gc, f: F)
            where
                F: FnOnce(&mut Gc),
            {
                self.0.scope(gc, f)
            }
        }

        self.check_collect(Scope1(roots, &def));
        self.alloc_owned(def)
    }

    /// Allocates a new object.
    pub fn alloc<D>(&mut self, def: D) -> Result<GcRef<D::Value>>
    where
        D: DataDef,
        D::Value: Sized + Any,
    {
        self.alloc_owned(def).map(GcRef::from)
    }

    pub fn alloc_owned<D>(&mut self, def: D) -> Result<OwnedGcRef<D::Value>>
    where
        D: DataDef,
        D::Value: Sized + Any,
    {
        let size = def.size();
        let needed = self.allocated_memory.saturating_add(size);
        if needed >= self.memory_limit {
            return Err(Error::OutOfMemory {
                limit: self.memory_limit,
                needed: needed,
            });
        }
        Ok(self.alloc_ignore_limit_(size, def))
    }

    pub fn alloc_ignore_limit<D>(&mut self, def: D) -> GcRef<D::Value>
    where
        D: DataDef,
        D::Value: Sized + Any,
    {
        GcRef::from(self.alloc_ignore_limit_(def.size(), def))
    }

    fn get_type_info(
        &mut self,
        tag: Option<&InternedStr>,
        fields: Option<&[InternedStr]>,
        type_id: TypeId,
        drop: unsafe fn(*mut ()),
    ) -> *const TypeInfo {
        match fields {
            Some(fields) => match self
                .record_infos
                .get(fields)
                .map(|info| &**info as *const _)
            {
                Some(info) => info,
                None => {
                    let owned_fields: Arc<[InternedStr]> = Arc::from(
                        fields
                            .iter()
                            .map(|v| unsafe { v.clone_unrooted() })
                            .collect::<Vec<_>>(),
                    );
                    &**self
                        .record_infos
                        .entry(owned_fields.clone())
                        .or_insert(Box::new(TypeInfo {
                            drop,
                            generation: self.generation,
                            tag: unsafe { tag.map(|tag| tag.clone_unrooted()) },
                            fields: unsafe {
                                fields
                                    .iter()
                                    .enumerate()
                                    .map(|(i, ref s)| (s.clone_unrooted(), i as VmIndex))
                                    .collect()
                            },
                            fields_key: owned_fields,
                        }))
                }
            },
            None => match tag {
                Some(tag) => match self.tag_infos.entry(unsafe { tag.clone_unrooted() }) {
                    Entry::Occupied(entry) => &**entry.get(),
                    Entry::Vacant(entry) => &**entry.insert(Box::new(TypeInfo {
                        drop,
                        generation: self.generation,
                        tag: Some(unsafe { tag.clone_unrooted() }),
                        fields: FnvMap::default(),
                        fields_key: Arc::from(Vec::new()),
                    })),
                },
                None => match self.type_infos.entry(type_id) {
                    Entry::Occupied(entry) => &**entry.get(),
                    Entry::Vacant(entry) => &**entry.insert(Box::new(TypeInfo {
                        drop,
                        generation: self.generation,
                        tag: None,
                        fields: FnvMap::default(),
                        fields_key: Arc::from(Vec::new()),
                    })),
                },
            },
        }
    }

    fn alloc_ignore_limit_<D>(&mut self, size: usize, def: D) -> OwnedGcRef<D::Value>
    where
        D: DataDef,
        D::Value: Sized + Any,
    {
        unsafe fn drop<T>(t: *mut ()) {
            ptr::drop_in_place(t as *mut T);
        }

        let type_info = self.get_type_info(
            def.tag(),
            def.fields(),
            TypeId::of::<D::Value>(),
            drop::<D::Value>,
        );

        let mut ptr = AllocPtr::new::<D::Value>(type_info, size);
        ptr.next = self.values.take();
        self.allocated_memory += ptr.size();
        unsafe {
            let p: *mut D::Value = D::Value::make_ptr(&def, ptr.value());
            let ret: *const D::Value = &*def.initialize(WriteOnly::new(p));
            // Check that the returned pointer is the same as the one we sent as an extra precaution
            // that the pointer was initialized
            assert!(ret == p);
            self.values = Some(ptr);
            let mut ptr = OwnedPtr(NonNull::new_unchecked(p));
            D::Value::unroot(&mut ptr);
            OwnedGcRef::with_root(ptr, self)
        }
    }

    pub unsafe fn check_collect<R>(&mut self, roots: R) -> bool
    where
        R: Trace + CollectScope,
    {
        if self.allocated_memory >= self.collect_limit {
            self.collect(roots);
            true
        } else {
            false
        }
    }

    /// Does a mark and sweep collection by walking from `roots`. This function is unsafe since
    /// roots need to cover all reachable object.
    pub unsafe fn collect<R>(&mut self, roots: R)
    where
        R: Trace + CollectScope,
    {
        info!("Start collect {:?}", self.generation);
        roots.scope(self, |self_| {
            roots.trace(self_);
            self_.sweep();
            self_.collect_limit = 2 * self_.allocated_memory;
        })
    }

    /// Marks the GcPtr
    /// Returns true if the pointer was already marked
    pub fn mark<T: ?Sized>(&mut self, value: &GcPtr<T>) -> bool {
        let header = value.header();
        // We only need to mark and trace values from this garbage collectors generation
        if header.generation().is_parent_of(self.generation()) || header.marked.get() {
            true
        } else {
            header.marked.set(true);
            false
        }
    }

    /// Clears out any unmarked pointers and resets marked pointers.
    ///
    /// Unsafe as it is up to the caller to make sure that all reachable pointers have been marked
    pub unsafe fn sweep(&mut self) {
        fn moving<T>(t: T) -> T {
            t
        }

        let mut count = 0;
        let mut free_count = 0;

        let mut first = self.values.take();
        {
            // Pointer to the current pointer (if it exists)
            let mut maybe_header = &mut first;
            loop {
                let mut free = false;
                let mut replaced_next = None;
                match *maybe_header {
                    Some(ref mut header) => {
                        // If the current pointer is not marked we take the rest of the list and
                        // move it to `replaced_next`
                        if !header.marked.get() {
                            replaced_next = header.next.take();
                            free = true;
                        } else {
                            header.marked.set(false);
                        }
                    }
                    // Reached the end of the list
                    None => break,
                }
                count += 1;
                if free {
                    free_count += 1;
                    // Free the current pointer
                    self.free(maybe_header.take());
                    *maybe_header = replaced_next;
                } else {
                    // Just move to the next pointer
                    maybe_header = &mut moving(maybe_header).as_mut().unwrap().next;
                }
            }
        }
        info!("GC: Freed {} / Traversed {}", free_count, count);
        self.values = first;
    }

    // Drop all values.
    //
    // SAFETY: No `GcPtr` allocated from this Gc must be reachable after calling this
    pub unsafe fn clear(&mut self) {
        self.values = None;
    }

    fn free(&mut self, header: Option<AllocPtr>) {
        if let Some(ref ptr) = header {
            self.allocated_memory -= ptr.size();
        }
        debug!("FREE: {:?}", header);
        drop(header);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::fmt;
    use std::mem;
    use std::rc::Rc;
    use std::usize;

    use self::Value::*;

    impl CollectScope for () {
        fn scope<F>(&self, gc: &mut Gc, f: F)
        where
            F: FnOnce(&mut Gc),
        {
            f(gc)
        }
    }

    impl<'a, T> CollectScope for &'a mut [T] {
        fn scope<F>(&self, gc: &mut Gc, f: F)
        where
            F: FnOnce(&mut Gc),
        {
            f(gc)
        }
    }

    fn object_count(gc: &Gc) -> usize {
        let mut header: &GcHeader = match gc.values {
            Some(ref x) => &**x,
            None => return 0,
        };
        let mut count = 1;
        loop {
            match header.next {
                Some(ref ptr) => {
                    count += 1;
                    header = &**ptr;
                }
                None => break,
            }
        }
        count
    }

    #[derive(Trace)]
    #[gluon(gluon_vm)]
    struct Data_ {
        fields: GcPtr<Vec<Value>>,
    }

    impl PartialEq for Data_ {
        fn eq(&self, other: &Data_) -> bool {
            self.fields.0 == other.fields.0
        }
    }
    impl fmt::Debug for Data_ {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.fields.0.fmt(f)
        }
    }

    struct Def<'a> {
        elems: &'a [Value],
    }
    unsafe impl<'a> DataDef for Def<'a> {
        type Value = Vec<Value>;
        fn size(&self) -> usize {
            mem::size_of::<Self::Value>()
        }
        fn initialize(self, result: WriteOnly<Vec<Value>>) -> &mut Vec<Value> {
            unsafe { result.write(self.elems.iter().map(|v| v.clone_unrooted()).collect()) }
        }
    }

    #[derive(PartialEq, Debug, Trace)]
    #[gluon(gluon_vm)]
    enum Value {
        Int(i32),
        Data(Data_),
    }

    unsafe impl CopyUnrooted for Value {}

    impl CloneUnrooted for Value {
        type Value = Self;
        #[inline]
        unsafe fn clone_unrooted(&self) -> Self {
            self.copy_unrooted()
        }
    }

    fn new_data(p: GcRef<Vec<Value>>) -> Value {
        unsafe {
            Data(Data_ {
                fields: p.unrooted(),
            })
        }
    }

    #[test]
    fn gc_header() {
        let mut gc: Gc = Gc::new(Generation::default(), usize::MAX);
        let ptr = unsafe { gc.alloc(Def { elems: &[Int(1)] }).unwrap().unrooted() };
        let header: *const _ = ptr.header();
        let other: &mut GcHeader = gc.values.as_mut().unwrap();
        assert_eq!(&*ptr as *const _ as *const (), other.value());
        assert_eq!(header, other as *const _);

        unsafe { gc.clear() }
    }

    #[test]
    fn basic() {
        let mut gc: Gc = Gc::new(Generation::default(), usize::MAX);
        let mut stack: Vec<Value> = Vec::new();
        stack.push(new_data(gc.alloc(Def { elems: &[Int(1)] }).unwrap()));
        let d2 = new_data(
            gc.alloc(Def {
                elems: std::slice::from_ref(&stack[0]),
            })
            .unwrap(),
        );
        stack.push(d2);
        assert_eq!(object_count(&gc), 2);
        unsafe {
            gc.collect(&mut *stack);
        }
        assert_eq!(object_count(&gc), 2);
        match stack[0] {
            Data(ref data) => assert_eq!(data.fields[0], Int(1)),
            _ => ice!(),
        }
        match stack[1] {
            Data(ref data) => assert_eq!(data.fields[0], stack[0]),
            _ => ice!(),
        }
        stack.pop();
        stack.pop();
        unsafe {
            gc.collect(&mut *stack);
        }
        assert_eq!(object_count(&gc), 0);

        unsafe { gc.clear() }
    }

    #[derive(Trace)]
    #[gluon(gluon_vm)]
    pub struct Dropable {
        dropped: Rc<Cell<bool>>,
    }

    impl Drop for Dropable {
        fn drop(&mut self) {
            self.dropped.set(true);
        }
    }

    #[test]
    fn drop() {
        let dropped = Rc::new(Cell::new(false));
        let mut gc = Gc::new(Generation::default(), usize::MAX);
        {
            let ptr = gc
                .alloc(Move(Dropable {
                    dropped: dropped.clone(),
                }))
                .unwrap();
            assert_eq!(false, ptr.dropped.get());
        }
        assert_eq!(false, dropped.get());
        unsafe {
            gc.collect(());
        }
        assert_eq!(true, dropped.get());

        unsafe { gc.clear() }
    }
}
