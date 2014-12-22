use std::ptr::RawPtr;
use std::mem;
use std::ptr;
use std::rt::heap::{allocate, deallocate};


pub struct Gc {
    values: Option<AllocPtr>,
    allocated_objects: uint,
    collect_limit: uint
}

pub trait DataDef<Sized? Result> {
    fn size(&self) -> uint;
    fn initialize(self, ptr: *mut Result);
    fn make_ptr(&self, ptr: *mut ()) -> *mut Result;
}

struct GcHeader {
    next: Option<AllocPtr>,
    value_size: uint,
    marked: bool,
}


struct AllocPtr {
    ptr: *mut GcHeader
}

impl AllocPtr {
    fn new(value_size: uint) -> AllocPtr {
        unsafe {
            let ptr = allocate(GcHeader::value_offset() + value_size, mem::align_of::<f64>());
            let ptr: *mut GcHeader = mem::transmute(ptr);
            ptr::write(ptr, GcHeader { next: None, value_size: value_size, marked: false });
            AllocPtr { ptr: ptr }
        }
    }
}

#[unsafe_destructor]
impl Drop for AllocPtr {
    
    fn drop(&mut self) {
        unsafe {
            ptr::read(&*self.ptr);
            let size = GcHeader::value_offset() + self.value_size;
            deallocate(mem::transmute::<*mut GcHeader, *mut u8>(self.ptr), size, mem::align_of::<f64>());
        }
    }
}

impl Deref<GcHeader> for AllocPtr {
    fn deref(&self) -> &GcHeader {
        unsafe { & *self.ptr }
    }
}

impl DerefMut<GcHeader> for AllocPtr {
    fn deref_mut(&mut self) -> &mut GcHeader {
        unsafe { &mut *self.ptr }
    }
}

impl GcHeader {

    fn value(&self) -> *mut () {
        unsafe {
            let ptr: *mut u8 = mem::transmute(self);
            ptr.offset(GcHeader::value_offset() as int) as *mut ()
        }
    }

    fn value_offset() -> uint {
        let hs = mem::size_of::<GcHeader>();
        let max_align = mem::align_of::<f64>();
        hs + ((max_align - (hs % max_align)) % max_align)
    }
}


pub struct GcPtr<Sized? T> {
    ptr: *mut T
}

impl <Sized? T> Copy for GcPtr<T> {}

impl <Sized? T> Clone for GcPtr<T> {
    fn clone(&self) -> GcPtr<T> {
        GcPtr { ptr: self.ptr }
    }
}

impl <Sized? T> Deref<T> for GcPtr<T> {
    fn deref(&self) -> &T {
        unsafe { & *self.ptr }
    }
}

impl <Sized? T> DerefMut<T> for GcPtr<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.ptr }
    }
}

impl <Sized? T> ::std::borrow::BorrowFrom<GcPtr<T>> for T {
    fn borrow_from(ptr: &GcPtr<T>) -> &T {
        &**ptr
    }
}

impl <Sized? T: Eq> Eq for GcPtr<T> { }
impl <Sized? T: PartialEq> PartialEq for GcPtr<T> {
    fn eq(&self, other: &GcPtr<T>) -> bool { **self == **other }
}

impl <S: ::std::hash::Writer, Sized? T: ::std::hash::Hash<S>> ::std::hash::Hash<S> for GcPtr<T> {
    fn hash(&self, state: &mut S) {
        (**self).hash(state)
    }
}

///Trait which must be implemented on all root types which contain GcPtr
///The type implementing Traverseable must call traverse on each of its fields
///which in turn contains GcPtr
pub trait Traverseable for Sized? {
    fn traverse(&mut self, func: &mut Gc);
}

impl Traverseable for () {
    fn traverse(&mut self, _: &mut Gc) {}
}

impl Traverseable for str {
    fn traverse(&mut self, _: &mut Gc) { }
}

impl <U> Traverseable for [U]
    where U: Traverseable {
    fn traverse(&mut self, f: &mut Gc) {
        for x in self.iter_mut() {
            x.traverse(f);
        }
    }
}

///When traversing a GcPtr we need to mark it
impl <Sized? T> Traverseable for GcPtr<T>
    where T: Traverseable {
    fn traverse(&mut self, gc: &mut Gc) {
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
    pub fn alloc_and_collect<Sized? T, Sized? R, D>(&mut self, roots: &mut R, mut def: D) -> GcPtr<T>
        where T: Traverseable, R: Traverseable, D: DataDef<T> + Traverseable {
        if self.allocated_objects >= self.collect_limit {
            self.collect2(roots, &mut def);
        }
        self.alloc(def)
    }

    pub fn alloc<Sized? T, D>(&mut self, def: D) -> GcPtr<T>
        where D: DataDef<T> {
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

    pub fn collect<Sized? R>(&mut self, roots: &mut R)
        where R: Traverseable {
        self.collect2(roots, &mut ());
    }
    
    fn collect2<Sized? R, D>(&mut self, roots: &mut R, def: &mut D)
        where R: Traverseable, D: Traverseable {
        roots.traverse(self);
        def.traverse(self);
        self.sweep();
    }

    ///Marks the GcPtr
    ///Returns true if the pointer was already marked
    fn mark<Sized? T>(&mut self, mut value: GcPtr<T>) -> bool {
        let header = unsafe { Gc::gc_header(&mut value) };
        if header.marked {
            return true
        }
        else {
            header.marked = true;
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
                        if !header.marked {
                            let unreached = mem::replace(current, header.next.take());
                            self.free(unreached);
                            continue
                        }
                        else {
                            header.marked = false;
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
        drop(header);
    }

    unsafe fn gc_header<Sized? T>(value: &mut GcPtr<T>) -> &mut GcHeader {
        debug!("HEADER");
        let p: *mut u8 = mem::transmute_copy(&value.ptr);
        debug!("{} {}", mem::transmute::<*mut u8, uint>(p), mem::transmute::<*mut u8, uint>(p.offset(8)));
        let header = p.offset(-(GcHeader::value_offset() as int));
        mem::transmute(header)
    }

}


#[cfg(test)]
mod tests {
    use super::{Gc, GcPtr, GcHeader, Traverseable, DataDef};
    use std::fmt;

    use self::Value::*;

    struct Data_ {
        fields: GcPtr<Vec<Value>>
    }

    impl Copy for Data_ { }

    impl  Deref<Vec<Value>> for Data_ {
        fn deref(&self) -> &Vec<Value> {
            &*self.fields
        }
    }
    impl  DerefMut<Vec<Value>> for Data_ {
        fn deref_mut(&mut self) -> &mut Vec<Value> {
            &mut *self.fields
        }
    }
    impl  PartialEq for Data_ {
        fn eq(&self, other: &Data_) -> bool {
            self.fields.ptr == other.fields.ptr
        }
    }
    impl  fmt::Show for Data_ {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.fields.ptr.fmt(f)
        }
    }

    struct Def<'a> {
        elems: &'a [Value]
    }
    impl <'a> DataDef<Vec<Value>> for Def<'a> {
        fn size(&self) -> uint {
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
            unsafe {
                ::std::mem::transmute(ptr)
            }
        }
    }

    #[deriving(PartialEq, Show)]
    enum Value {
        Int(int),
        Data(Data_)
    }

    impl Copy for Value { }

    impl Traverseable for Vec<Value> {
        fn traverse(&mut self, gc: &mut Gc) {
            for v in self.iter_mut() {
                match *v {
                    Data(ref mut data) => {
                        gc.mark(data.fields);
                    }
                    _ => ()
                }
            }
        }
    }
    impl Traverseable for Value {
        fn traverse(&mut self, gc: &mut Gc) {
            match *self {
                Data(ref mut data) => {
                    gc.mark(data.fields);
                }
                _ => ()
            }
        }
    }

    fn num_objects(gc: &Gc) -> uint {
        let mut header: &GcHeader = match gc.values {
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

    fn new_data(p: GcPtr<Vec<Value>>) -> Value {
        Data(Data_ { fields: p })
    }

    #[test]
    fn gc_header() {
        let mut gc: Gc = Gc::new();
        let mut ptr = gc.alloc(Def { elems: &[Int(1)] });
        let header: *mut _ = unsafe { &mut *Gc::gc_header(&mut ptr) };
        let other: *mut _ = &mut **gc.values.as_mut().unwrap();
        assert_eq!(header, other);
    }

    #[test]
    fn basic() {
        let mut gc: Gc = Gc::new();
        let mut stack: Vec<Value> = Vec::new();
        stack.push(new_data(gc.alloc(Def { elems: &[Int(1)] })));
        let d2 = new_data(gc.alloc(Def { elems: &[stack[0]] }));
        stack.push(d2);
        assert_eq!(num_objects(&gc), 2);
        gc.collect(&mut stack);
        assert_eq!(num_objects(&gc), 2);
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
        gc.collect(&mut stack);
        assert_eq!(num_objects(&gc), 0);
    }
}
