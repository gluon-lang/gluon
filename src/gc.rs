use std::ptr::PtrExt;
use std::fmt;
use std::mem;
use std::ptr;
use std::hash::{Hash, Hasher};
use std::rt::heap::{allocate, deallocate};
use std::ops::{Deref, DerefMut};
use std::cell::Cell;


#[derive(Debug)]
pub struct Gc {
    values: Option<AllocPtr>,
    allocated_objects: usize,
    collect_limit: usize
}

pub unsafe trait DataDef {
    type Value: ?Sized;
    fn size(&self) -> usize;
    fn initialize(self, ptr: *mut <Self as DataDef>::Value);
    fn make_ptr(&self, ptr: *mut ()) -> *mut <Self as DataDef>::Value;
}

///Datadefinition that moves its value directly into the pointer
///useful for sized types
pub struct Move<T>(pub T);

unsafe impl <T> DataDef for Move<T> {
    type Value = T;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<T>()
    }
    fn initialize(self, result: *mut T) {
        unsafe {
            ::std::ptr::write(result, self.0);
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut T {
        ptr as *mut T
    }
}

#[derive(Debug)]
struct GcHeader {
    next: Option<AllocPtr>,
    value_size: Cell<usize>,
    marked: Cell<bool>,
}


struct AllocPtr {
    ptr: *mut GcHeader
}

impl AllocPtr {
    fn new(value_size: usize) -> AllocPtr {
        unsafe {
            let alloc_size = GcHeader::value_offset() + value_size;
            let ptr = allocate(alloc_size, mem::align_of::<f64>()) as *mut GcHeader;
            ptr::write(ptr, GcHeader {
                next: None,
                value_size: Cell::new(value_size),
                marked: Cell::new(false)
            });
            AllocPtr { ptr: ptr }
        }
    }
}

impl fmt::Debug for AllocPtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AllocPtr {{ ptr: {:?} }}", &**self)
    }
}

#[unsafe_destructor]
impl Drop for AllocPtr {
    
    fn drop(&mut self) {
        unsafe {
            ptr::read(&*self.ptr);
            let size = GcHeader::value_offset() + self.value_size.get();
            deallocate(self.ptr as *mut u8, size, mem::align_of::<f64>());
        }
    }
}

impl Deref for AllocPtr {
    type Target = GcHeader;
    fn deref(&self) -> &GcHeader {
        unsafe { & *self.ptr }
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
            let bytes = (self as *const GcHeader) as *mut u8;
            bytes.offset(GcHeader::value_offset() as isize) as *mut ()
        }
    }

    fn value_offset() -> usize {
        let hs = mem::size_of::<GcHeader>();
        let max_align = mem::align_of::<f64>();
        hs + ((max_align - (hs % max_align)) % max_align)
    }
}


pub struct GcPtr<T: ?Sized> {
    ptr: *const T
}

impl <T: ?Sized> Copy for GcPtr<T> {}

impl <T: ?Sized> Clone for GcPtr<T> {
    fn clone(&self) -> GcPtr<T> {
        GcPtr { ptr: self.ptr }
    }
}

impl <T: ?Sized> Deref for GcPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { & *self.ptr }
    }
}

impl <T: ?Sized> ::std::borrow::Borrow<T> for GcPtr<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl <T: ?Sized + Eq> Eq for GcPtr<T> { }
impl <T: ?Sized + PartialEq> PartialEq for GcPtr<T> {
    fn eq(&self, other: &GcPtr<T>) -> bool { **self == **other }
}

impl <T: ?Sized + Hash> Hash for GcPtr<T> {
    fn hash<H>(&self, state: &mut H)
        where H: Hasher {
        (**self).hash(state)
    }
}

///Trait which must be implemented on all root types which contain GcPtr
///The type implementing Traverseable must call traverse on each of its fields
///which in turn contains GcPtr
pub trait Traverseable {
    fn traverse(&self, func: &mut Gc);
}

impl <'a, T> Traverseable for &'a T
    where T: Traverseable {
    fn traverse(&self, gc: &mut Gc) { (**self).traverse(gc); }
}

impl Traverseable for () {
    fn traverse(&self, _: &mut Gc) { }
}
impl Traverseable for u8 {
    fn traverse(&self, _: &mut Gc) { }
}

impl Traverseable for str {
    fn traverse(&self, _: &mut Gc) { }
}

impl <T> Traverseable for Cell<T>
    where T: Traverseable + Copy {
    fn traverse(&self, f: &mut Gc) {
        self.get().traverse(f);
    }
}

impl <U> Traverseable for [U]
    where U: Traverseable {
    fn traverse(&self, f: &mut Gc) {
        for x in self.iter() {
            x.traverse(f);
        }
    }
}

///When traversing a GcPtr we need to mark it
impl <T: ?Sized> Traverseable for GcPtr<T>
    where T: Traverseable {
    fn traverse(&self, gc: &mut Gc) {
        if !gc.mark(*self) {
            //Continue traversing if this ptr was not already marked
            (**self).traverse(gc);
        }
    }
}

impl Gc {

    pub fn new() -> Gc {
        Gc { values: None, allocated_objects: 0, collect_limit: 100 }
    }

    ///Unsafe since it calls collects if memory needs to be collected
    pub unsafe fn alloc_and_collect<T: ?Sized, R: ?Sized, D>(&mut self, roots: &mut R, mut def: D) -> GcPtr<T>
        where R: Traverseable, D: DataDef<Value=T> + Traverseable {
        if self.allocated_objects >= self.collect_limit {
            self.collect2(roots, &mut def);
        }
        self.alloc(def)
    }

    pub fn alloc<T: ?Sized, D>(&mut self, def: D) -> GcPtr<T>
        where D: DataDef<Value=T> {
        debug!("ALLOC: {}, size: {}", unsafe {
            let desc = ::std::intrinsics::get_tydesc::<T>();
            if desc.is_null() {
                "<unknown>"
            }
            else {
                (*desc).name
            }
        }, def.size());

        let mut ptr = AllocPtr::new(def.size());
        ptr.next = self.values.take();
        self.allocated_objects += 1;
        unsafe {
            let p: &mut T = &mut *def.make_ptr(ptr.value());
            def.initialize(p);
            self.values = Some(ptr);
            GcPtr { ptr: p }
        }
    }

    ///Does a mark and sweep collection by walking from `roots`. This function is unsafe since
    ///roots need to cover all reachable object.
    pub unsafe fn collect<R: ?Sized>(&mut self, roots: &mut R)
        where R: Traverseable {
        self.collect2(roots, &mut ());
    }


    pub fn object_count(&self) -> usize {
        let mut header: &GcHeader = match self.values {
            Some(ref x) => &**x,
            None => return 0
        };
        let mut count = 1;
        loop {
            match header.next {
                Some(ref ptr) => {
                    count += 1;
                    header = &**ptr;
                }
                None => break
            }
        }
        count
    }

    
    fn collect2<R: ?Sized, D>(&mut self, roots: &mut R, def: &mut D)
        where R: Traverseable, D: Traverseable {
        roots.traverse(self);
        def.traverse(self);
        self.sweep();
    }

    ///Marks the GcPtr
    ///Returns true if the pointer was already marked
    fn mark<T: ?Sized>(&mut self, value: GcPtr<T>) -> bool {
        let header = unsafe { Gc::gc_header(&value) };
        if header.marked.get() {
            return true
        }
        else {
            header.marked.set(true);
            return false
        }
    }

    fn sweep(&mut self) {
        //Usage of unsafe are sadly needed to circumvent the borrow checker
        let mut first = self.values.take();
        {
            let mut maybe_header = &mut first;
            loop {
                let current: &mut Option<AllocPtr> = unsafe { mem::transmute(&*maybe_header) };
                maybe_header = match *maybe_header {
                    Some(ref mut header) => {
                        if !header.marked.get() {
                            let unreached = mem::replace(current, header.next.take());
                            self.free(unreached);
                            continue
                        }
                        else {
                            header.marked.set(false);
                            let next: &mut Option<AllocPtr> = unsafe { mem::transmute(&mut header.next) };
                            next
                        }
                    }
                    None => break
                };
            }
        }
        self.values = first;
    }
    fn free(&mut self, header: Option<AllocPtr>) {
        self.allocated_objects -= 1;
        debug!("FREE: {:?}", header);
        drop(header);
    }

    unsafe fn gc_header<T: ?Sized>(value: &GcPtr<T>) -> &GcHeader {
        //Use of transmute_copy allows us to get the pointer
        //to the data regardless of wether T is unsized or not
        //(DST is structured as (ptr, len))
        //TODO: Better way of doing this?
        let p: *mut u8 = mem::transmute_copy(&value.ptr);
        let header = p.offset(-(GcHeader::value_offset() as isize));
        &*(header as *const GcHeader)
    }
}


#[cfg(test)]
mod tests {
    use super::{Gc, GcPtr, Traverseable, DataDef};
    use std::ops::Deref;
    use std::fmt;

    use self::Value::*;

    struct Data_ {
        fields: GcPtr<Vec<Value>>
    }

    impl Copy for Data_ { }

    impl Deref for Data_ {
        type Target = Vec<Value>;
        fn deref(&self) -> &Vec<Value> {
            &*self.fields
        }
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
        elems: &'a [Value]
    }
    unsafe impl <'a> DataDef for Def<'a> {
        type Value = Vec<Value>;
        fn size(&self) -> usize {
            use std::mem::size_of;
            self.elems.len() * size_of::<Value>()
        }
        fn initialize(self, result: *mut Vec<Value>) {
            let vec = self.elems.iter().map(|x| *x).collect();
            unsafe {
                ::std::ptr::write(result, vec);
            }
        }
        fn make_ptr(&self, ptr: *mut ()) -> *mut Vec<Value> {
            ptr as *mut _
        }
    }

    #[derive(PartialEq, Debug)]
    enum Value {
        Int(i32),
        Data(Data_)
    }

    impl Copy for Value { }

    impl Traverseable for Vec<Value> {
        fn traverse(&self, gc: &mut Gc) {
            for v in self.iter() {
                match *v {
                    Data(ref data) => {
                        gc.mark(data.fields);
                    }
                    _ => ()
                }
            }
        }
    }
    impl Traverseable for Value {
        fn traverse(&self, gc: &mut Gc) {
            match *self {
                Data(ref data) => {
                    gc.mark(data.fields);
                }
                _ => ()
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
        let header: *const _ = unsafe { Gc::gc_header(&ptr) };
        let other: *const _ = &**gc.values.as_mut().unwrap();
        assert_eq!(header, other);
    }

    #[test]
    fn basic() {
        let mut gc: Gc = Gc::new();
        let mut stack: Vec<Value> = Vec::new();
        stack.push(new_data(gc.alloc(Def { elems: &[Int(1)] })));
        let d2 = new_data(gc.alloc(Def { elems: &[stack[0]] }));
        stack.push(d2);
        assert_eq!(gc.object_count(), 2);
        unsafe { gc.collect(&mut stack); }
        assert_eq!(gc.object_count(), 2);
        match stack[0] {
            Data(ref data) => assert_eq!((**data)[0], Int(1)),
            _ => panic!()
        }
        match stack[1] {
            Data(ref data) => assert_eq!((**data)[0], stack[0]),
            _ => panic!()
        }
        stack.pop();
        stack.pop();
        unsafe { gc.collect(&mut stack); }
        assert_eq!(gc.object_count(), 0);
    }
}
