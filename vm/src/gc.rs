use std::fmt;
use std::mem;
use std::ptr;
use std::collections::VecDeque;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::cell::Cell;
use std::any::Any;
use std::marker::PhantomData;


#[inline]
unsafe fn allocate(size: usize) -> *mut u8 {
    // Allocate an extra element if it does not fit exactly
    let cap = size / mem::size_of::<f64>() +
              (if size % mem::size_of::<f64>() != 0 {
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
    let cap = old_size / mem::size_of::<f64>() +
              (if old_size % mem::size_of::<f64>() != 0 {
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
    unsafe fn new(t: *mut T) -> WriteOnly<'s, T> {
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

/// A mark and sweep garbage collector.
#[derive(Debug)]
pub struct Gc {
    /// Linked list of all objects allocted by this garbage collector.
    values: Option<AllocPtr>,
    allocated_memory: usize,
    collect_limit: usize,
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
    type Value: ?Sized + for<'a> FromPtr<&'a Self>;
    /// Returns how many bytes need to be allocted for this `DataDef`
    fn size(&self) -> usize;
    /// Consumes `self` to initialize the allocated value.
    /// Returns the initialized pointer.
    fn initialize<'w>(self, ptr: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value;
}

/// `DataDef` that moves its value directly into the pointer
/// useful for sized types
pub struct Move<T>(pub T);

unsafe impl<T> DataDef for Move<T> {
    type Value = T;
    fn size(&self) -> usize {
        mem::size_of::<T>()
    }
    fn initialize(self, result: WriteOnly<T>) -> &mut T {
        result.write(self.0)
    }
}

unsafe impl<'s, T: Copy> DataDef for &'s [T] {
    type Value = [T];
    fn size(&self) -> usize {
        self.len() * mem::size_of::<T>()
    }
    fn initialize(self, result: WriteOnly<[T]>) -> &mut [T] {
        result.write_slice(self)
    }
}

#[derive(Debug)]
struct GcHeader {
    next: Option<AllocPtr>,
    value_size: usize,
    marked: Cell<bool>,
}


struct AllocPtr {
    ptr: *mut GcHeader,
}

impl AllocPtr {
    fn new(value_size: usize) -> AllocPtr {
        unsafe {
            let alloc_size = GcHeader::value_offset() + value_size;
            let ptr = allocate(alloc_size) as *mut GcHeader;
            ptr::write(ptr,
                       GcHeader {
                           next: None,
                           value_size: value_size,
                           marked: Cell::new(false),
                       });
            AllocPtr { ptr: ptr }
        }
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
    fn value(&self) -> *mut () {
        unsafe {
            let ptr: *const GcHeader = self;
            (ptr as *mut u8).offset(GcHeader::value_offset() as isize) as *mut ()
        }
    }

    fn value_offset() -> usize {
        let hs = mem::size_of::<GcHeader>();
        let max_align = mem::align_of::<f64>();
        hs + ((max_align - (hs % max_align)) % max_align)
    }
}

/// A pointer to a garbage collected value.
///
/// It is only safe to access data through a `GcPtr` if the value is rooted (stored in a place
/// where the garbage collector will find it during the mark phase).
pub struct GcPtr<T: ?Sized> {
    // TODO Use NonZero to allow for better optimizing
    ptr: *const T,
}

impl<T: ?Sized> Copy for GcPtr<T> {}

impl<T: ?Sized> Clone for GcPtr<T> {
    fn clone(&self) -> GcPtr<T> {
        GcPtr { ptr: self.ptr }
    }
}

impl<T: ?Sized> Deref for GcPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
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
        where H: Hasher
    {
        (**self).hash(state)
    }
}
impl<T: ?Sized + fmt::Debug> fmt::Debug for GcPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "GcPtr({:?})", &**self)
    }
}
impl<T: ?Sized + fmt::Display> fmt::Display for GcPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: ?Sized> GcPtr<T> {
    fn header(&self) -> &GcHeader {
        // Use of transmute_copy allows us to get the pointer
        // to the data regardless of wether T is unsized or not
        // (DST is structured as (ptr, len))
        // This function should always be safe to call as GcPtr's should always have a header
        // TODO: Better way of doing this?
        unsafe {
            let p: *mut u8 = mem::transmute_copy(&self.ptr);
            let header = p.offset(-(GcHeader::value_offset() as isize));
            &*(header as *const GcHeader)
        }
    }
}

impl<'a, T: Traverseable + 'a> GcPtr<T> {
    /// Coerces `self` to a `Traverseable` trait object
    pub fn as_traverseable(self) -> GcPtr<Traverseable + 'a> {
        GcPtr { ptr: self.ptr as *const Traverseable }
    }
}
impl GcPtr<str> {
    /// Coerces `self` to a `Traverseable` trait object
    pub fn as_traverseable_string(self) -> GcPtr<Traverseable> {
        // As there is nothing to traverse in a str we can safely cast it to *const u8 and use
        // u8's Traverseable impl
        GcPtr { ptr: self.as_ptr() as *const Traverseable }
    }
}

/// Trait which must be implemented on all root types which contain `GcPtr`
/// A type implementing Traverseable must call traverse on each of its fields
/// which in turn contains `GcPtr`
pub trait Traverseable {
    fn traverse(&self, gc: &mut Gc) {
        let _ = gc;
    }
}

impl<T> Traverseable for Move<T>
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc)
    }
}

impl<T: ?Sized> Traverseable for Box<T>
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        (**self).traverse(gc)
    }
}

impl<'a, T: ?Sized> Traverseable for &'a T
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        (**self).traverse(gc);
    }
}

impl<'a, T: ?Sized> Traverseable for &'a mut T
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        (**self).traverse(gc);
    }
}

macro_rules! tuple_traverse {
    () => {};
    ($first: ident $($id: ident)*) => {
        tuple_traverse!($($id)*);
        impl <$first $(,$id)*> Traverseable for ($first, $($id,)*)
            where $first: Traverseable
                  $(, $id: Traverseable)* {
            #[allow(non_snake_case)]
            fn traverse(&self, gc: &mut Gc) {
                let (ref $first, $(ref $id,)*) = *self;
                $first.traverse(gc);
                $(
                    $id.traverse(gc);
                )*
            }
        }
    }
}

tuple_traverse!(A B C D E F G H I J);

impl Traverseable for () {
    fn traverse(&self, _: &mut Gc) {}
}

impl Traverseable for Any {
    fn traverse(&self, _: &mut Gc) {}
}

impl Traverseable for u8 {
    fn traverse(&self, _: &mut Gc) {}
}

impl Traverseable for str {
    fn traverse(&self, _: &mut Gc) {}
}

impl<T: ?Sized> Traverseable for *const T {
    fn traverse(&self, _: &mut Gc) {}
}

impl<T: ?Sized> Traverseable for *mut T {
    fn traverse(&self, _: &mut Gc) {}
}

impl<T> Traverseable for Cell<T>
    where T: Traverseable + Copy
{
    fn traverse(&self, f: &mut Gc) {
        self.get().traverse(f);
    }
}

impl<U> Traverseable for [U]
    where U: Traverseable
{
    fn traverse(&self, f: &mut Gc) {
        for x in self.iter() {
            x.traverse(f);
        }
    }
}

impl<T> Traverseable for Vec<T>
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        (**self).traverse(gc);
    }
}

impl<T> Traverseable for VecDeque<T>
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        self.as_slices().traverse(gc);
    }
}

///When traversing a GcPtr we need to mark it
impl<T: ?Sized> Traverseable for GcPtr<T>
    where T: Traverseable
{
    fn traverse(&self, gc: &mut Gc) {
        if !gc.mark(*self) {
            // Continue traversing if this ptr was not already marked
            (**self).traverse(gc);
        }
    }
}

impl Gc {
    /// Constructs a new garbage collector
    pub fn new() -> Gc {
        Gc {
            values: None,
            allocated_memory: 0,
            collect_limit: 100,
        }
    }

    /// Allocates a new object. If the garbage collector has hit the collection limit a collection
    /// will occur.
    ///
    /// Unsafe since `roots` must be able to traverse all accesible `GcPtr` values.
    pub unsafe fn alloc_and_collect<R, D>(&mut self, roots: R, def: D) -> GcPtr<D::Value>
        where R: Traverseable,
              D: DataDef + Traverseable
    {
        if self.allocated_memory >= self.collect_limit {
            self.collect((roots, &def));
        }
        self.alloc(def)
    }

    /// Allocates a new object.
    pub fn alloc<D>(&mut self, def: D) -> GcPtr<D::Value>
        where D: DataDef
    {
        let size = def.size();
        let mut ptr = AllocPtr::new(size);
        ptr.next = self.values.take();
        self.allocated_memory += ptr.size();
        unsafe {
            let p: *mut D::Value = D::Value::make_ptr(&def, ptr.value());
            let ret: *const D::Value = &*def.initialize(WriteOnly::new(p));
            // Check that the returned pointer is the same as the one we sent as an extra precaution
            // that the pointer was initialized
            assert!(ret == p);
            self.values = Some(ptr);
            GcPtr { ptr: p }
        }
    }

    ///Does a mark and sweep collection by walking from `roots`. This function is unsafe since
    ///roots need to cover all reachable object.
    pub unsafe fn collect<R>(&mut self, roots: R)
        where R: Traverseable
    {
        debug!("Start collect");
        roots.traverse(self);
        self.sweep();
        self.collect_limit = 2 * self.allocated_memory;
    }

    ///Marks the GcPtr
    ///Returns true if the pointer was already marked
    pub fn mark<T: ?Sized>(&mut self, value: GcPtr<T>) -> bool {
        let header = value.header();
        if header.marked.get() {
            return true;
        } else {
            header.marked.set(true);
            return false;
        }
    }

    unsafe fn sweep(&mut self) {
        // Usage of unsafe are sadly needed to circumvent the borrow checker
        let mut first = self.values.take();
        {
            let mut maybe_header = &mut first;
            loop {
                let current: &mut Option<AllocPtr> = mem::transmute(&mut *maybe_header);
                maybe_header = match *maybe_header {
                    Some(ref mut header) => {
                        if !header.marked.get() {
                            let unreached = mem::replace(current, header.next.take());
                            self.free(unreached);
                            continue;
                        } else {
                            header.marked.set(false);
                            let next: &mut Option<AllocPtr> = mem::transmute(&mut header.next);
                            next
                        }
                    }
                    None => break,
                };
            }
        }
        self.values = first;
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
    use super::{Gc, GcPtr, GcHeader, Traverseable, DataDef, WriteOnly};
    use std::fmt;
    use std::mem;

    use self::Value::*;

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


    #[derive(Copy, Clone)]
    struct Data_ {
        fields: GcPtr<Vec<Value>>,
    }

    impl PartialEq for Data_ {
        fn eq(&self, other: &Data_) -> bool {
            self.fields.ptr == other.fields.ptr
        }
    }
    impl fmt::Debug for Data_ {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.fields.ptr.fmt(f)
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
            result.write(self.elems.to_owned())
        }
    }

    #[derive(Copy, Clone, PartialEq, Debug)]
    enum Value {
        Int(i32),
        Data(Data_),
    }

    impl Traverseable for Value {
        fn traverse(&self, gc: &mut Gc) {
            match *self {
                Data(ref data) => data.fields.traverse(gc),
                _ => (),
            }
        }
    }

    fn new_data(p: GcPtr<Vec<Value>>) -> Value {
        Data(Data_ { fields: p })
    }

    #[test]
    fn gc_header() {
        let mut gc: Gc = Gc::new();
        let ptr = gc.alloc(Def { elems: &[Int(1)] });
        let header: *const _ = ptr.header();
        let other: &GcHeader = gc.values.as_ref().unwrap();
        assert_eq!(&*ptr as *const _ as *const (), other.value());
        assert_eq!(header, other as *const _);
    }

    #[test]
    fn basic() {
        let mut gc: Gc = Gc::new();
        let mut stack: Vec<Value> = Vec::new();
        stack.push(new_data(gc.alloc(Def { elems: &[Int(1)] })));
        let d2 = new_data(gc.alloc(Def { elems: &[stack[0]] }));
        stack.push(d2);
        assert_eq!(object_count(&gc), 2);
        unsafe {
            gc.collect(&mut *stack);
        }
        assert_eq!(object_count(&gc), 2);
        match stack[0] {
            Data(ref data) => assert_eq!(data.fields[0], Int(1)),
            _ => panic!(),
        }
        match stack[1] {
            Data(ref data) => assert_eq!(data.fields[0], stack[0]),
            _ => panic!(),
        }
        stack.pop();
        stack.pop();
        unsafe {
            gc.collect(&mut *stack);
        }
        assert_eq!(object_count(&gc), 0);
    }
}
