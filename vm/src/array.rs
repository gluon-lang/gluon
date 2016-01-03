use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::slice;

use gc::{DataDef, Gc, Traverseable, WriteOnly};

enum Void {}

/// Abstract array type which have their length store inline with the elements.
/// Fills the same role as Box<[T]> but takes only 8 bytes on the stack instead of 16
pub struct Array<T> {
    len: usize,
    array_start: [T; 0],
    /// Prevents the array from being instantiated directly
    _void: Void,
}

impl<T> Drop for Array<T> {
    fn drop(&mut self) {
        unsafe {
            for value in self {
                ::std::ptr::read(value);
            }
        }
    }
}

impl<T> AsRef<[T]> for Array<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for Array<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: PartialEq> PartialEq for Array<T> {
    fn eq(&self, other: &Array<T>) -> bool {
        &**self == other.as_ref()
    }
}

impl<T: Eq> Eq for Array<T> {}

impl<T: PartialOrd> PartialOrd for Array<T> {
    fn partial_cmp(&self, other: &Array<T>) -> Option<Ordering> {
        (&**self).partial_cmp(other.as_ref())
    }
}

impl<T: Ord> Ord for Array<T> {
    fn cmp(&self, other: &Array<T>) -> Ordering {
        (&**self).cmp(other)
    }
}

impl<T: Hash> Hash for Array<T> {
    fn hash<H>(&self, hasher: &mut H)
        where H: Hasher
    {
        (&**self).hash(hasher)
    }
}

impl<T: fmt::Debug> fmt::Debug for Array<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &**self)
    }
}

impl<T: Traverseable> Traverseable for Array<T> {
    fn traverse(&self, gc: &mut Gc) {
        (**self).traverse(gc)
    }
}

impl<T> Array<T> {
    pub fn size_of(len: usize) -> usize {
        mem::size_of::<usize>() + mem::size_of::<T>() * len
    }

    /// Initializes an Array.
    /// To be safe it is required that the iterators length is known and exactly the same as the
    /// length of the allocated array.
    pub unsafe fn initialize<I>(&mut self, iterable: I)
        where I: IntoIterator<Item = T>,
              T: Clone
    {
        let iter = iterable.into_iter();
        self.len = iter.size_hint().1.expect("initialize expected a known length");
        for (field, value) in self.iter_mut().zip(iter) {
            *field = value;
        }
    }
}

impl<T> Deref for Array<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.array_start.as_ptr(), self.len) }
    }
}

impl<T> DerefMut for Array<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.array_start.as_mut_ptr(), self.len) }
    }
}

impl<'a, T: 'a> IntoIterator for &'a Array<T> {
    type Item = &'a T;
    type IntoIter = <&'a [T] as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&**self).into_iter()
    }
}

impl<'a, T: 'a> IntoIterator for &'a mut Array<T> {
    type Item = &'a mut T;
    type IntoIter = <&'a mut [T] as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&mut **self).into_iter()
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Str(Array<u8>);

impl fmt::Debug for Str {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &**self)
    }
}

impl fmt::Display for Str {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &**self)
    }
}

impl Traverseable for Str {
    fn traverse(&self, _: &mut Gc) {}
}

impl Deref for Str {
    type Target = str;
    fn deref(&self) -> &str {
        unsafe { ::std::str::from_utf8_unchecked(&self.0) }
    }
}

unsafe impl<'a> DataDef for &'a str {
    type Value = Str;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<usize>() + self.len()
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, Str>) -> &'w mut Str {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.0.len = self.len();
            for (field, value) in result.0.iter_mut().zip(self.as_bytes()) {
                *field = *value;
            }
            result
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut Str {
        ptr as *mut Str
    }
}
