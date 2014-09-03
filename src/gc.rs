use std::ptr;
use std::ptr::RawPtr;
use std::mem;


pub struct Gc<T> {
    values: Option<Box<GcHeader<T>>>,
    allocated_objects: uint,
    collect_limit: uint
}

#[deriving(Clone, PartialEq)]
struct GcHeader<T> {
    next: *mut GcHeader<T>,
    marked: bool,
    value: T
}

pub trait Traverseable<T> {
    fn traverse(&mut self, func: |&mut T|);
}

impl <T: Traverseable<T>> Gc<T> {

    pub fn new() -> Gc<T> {
        Gc { values: None, allocated_objects: 0, collect_limit: 100 }
    }
    
    pub fn alloc_and_collect<R: Traverseable<T>>(&mut self, roots: &mut R, value: T) -> *mut T {
        if self.allocated_objects >= self.collect_limit {
            self.collect(roots);
        }
        self.alloc(value)
    }
    pub fn alloc(&mut self, value: T) -> *mut T {
        let next_ptr: *mut GcHeader<T> = match self.values {
            Some(ref ptr) => unsafe { mem::transmute(&**ptr) },
            None => ptr::mut_null()
        };
        let new = Some(box GcHeader { next: next_ptr, marked: false, value: value });
        let next = mem::replace(&mut self.values, new);
        self.allocated_objects += 1;
        unsafe {
            mem::forget(next);
            &mut self.values.as_mut().unwrap().value
        }
    }

    pub fn collect<R: Traverseable<T>>(&mut self, roots: &mut R) {
        roots.traverse(|v| self.mark(v));
        self.sweep();
    }

    fn gc_header(value: &mut T) -> &mut GcHeader<T> {
        unsafe {
            let p: *mut u8 = mem::transmute(&mut *value);
            let header = p.offset(mem::size_of::<T>() as int - mem::size_of::<GcHeader<T>>() as int);
            mem::transmute(header)
        }
    }

    fn mark(&mut self, value: &mut T) {
        let header = Gc::gc_header(value);
        if !header.marked {
            header.marked = true;
            header.value.traverse(|child| self.mark(child));
        }
    }
    fn sweep<'a>(&mut self) {
        let mut first = self.values.take();
        {
            let mut maybe_header = &mut first;
            loop {
                maybe_header = match *maybe_header {
                    Some(ref mut header) => {
                        if !header.marked {
                            let next: Box<GcHeader<T>> = unsafe { mem::transmute(header.next) };
                            let unreached = mem::replace(header, next);
                            self.free(unreached);
                            continue
                        }
                        else {
                            header.marked = false;
                            let next: &mut Option<Box<GcHeader<T>>> = unsafe { mem::transmute(&mut header.next) };
                            next
                        }
                    }
                    None => break
                };
            }
        }
        self.values = first;
    }
    fn free(&mut self, header: Box<GcHeader<T>>) {
        self.allocated_objects -= 1;
        drop(header);
    }
}


#[cfg(test)]
mod tests {
    use super::{Gc, GcHeader, Traverseable};

    #[deriving(PartialEq, Show)]
    struct Data {
        fields: *mut Vec<Value>
    }
    impl Deref<Vec<Value>> for Data {
        fn deref(&self) -> &Vec<Value> {
            unsafe { &*self.fields }
        }
    }
    impl DerefMut<Vec<Value>> for Data {
        fn deref_mut(&mut self) -> &mut Vec<Value> {
            unsafe { &mut *self.fields }
        }
    }
    #[deriving(PartialEq, Show)]
    enum Value {
        Int(int),
        Data(Data)
    }
    impl Traverseable<Vec<Value>> for Vec<Value> {
        fn traverse(&mut self, func: |&mut Vec<Value>|) {
            for v in self.mut_iter() {
                match *v {
                    Data(ref mut data) => func(&mut **data),
                    _ => ()
                }
            }
        }
    }
    impl Traverseable<Vec<Value>> for Value {
        fn traverse(&mut self, func: |&mut Vec<Value>|) {
            match *self {
                Data(ref mut data) => func(&mut **data),
                _ => ()
            }
        }
    }

    fn num_objects<T>(gc: &Gc<T>) -> uint {
        let mut header: &GcHeader<T> = match gc.values {
            Some(ref x) => &**x,
            None => return 0
        };
        let mut count = 1;
        while header.next.is_not_null() {
            count += 1;
            header = unsafe { &*header.next };
        }
        count
    }

    fn new_data(p: *mut Vec<Value>) -> Value {
        Data(Data { fields: p })
    }

    #[test]
    fn gc_header() {
        let mut gc: Gc<Vec<Value>> = Gc::new();
        let ptr = gc.alloc(Vec::new());
        let header: *mut _ = &mut *Gc::gc_header(unsafe { &mut *ptr });
        let other: *mut _ = &mut *gc.values.unwrap();
        assert_eq!(header, other);
    }

    #[test]
    fn basic() {
        let mut gc: Gc<Vec<Value>> = Gc::new();
        let mut stack: Vec<Value> = Vec::new();
        stack.push(new_data(gc.alloc(vec![Int(1)])));
        let d2 = new_data(gc.alloc(vec![stack[0]]));
        stack.push(d2);
        assert_eq!(num_objects(&gc), 2);
        gc.collect(&mut stack);
        assert_eq!(num_objects(&gc), 2);
        match stack[0] {
            Data(ref data) => assert_eq!((**data)[0], Int(1)),
            _ => fail!()
        }
        match stack[1] {
            Data(ref data) => assert_eq!((**data)[0], stack[0]),
            _ => fail!()
        }
        stack.pop();
        stack.pop();
        gc.collect(&mut stack);
        assert_eq!(num_objects(&gc), 0);
    }
}
