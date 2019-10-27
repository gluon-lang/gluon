use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};
use std::slice;

use crate::gc::Trace;

mod internal {
    pub struct CantConstruct(());
}

/// Abstract array type which have their length store inline with the elements.
/// Fills the same role as Box<[T]> but takes only 8 bytes on the stack instead of 16
#[repr(C)]
pub struct Array<T> {
    len: usize,
    array_start: [T; 0],
    _marker: self::internal::CantConstruct,
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
    where
        H: Hasher,
    {
        (&**self).hash(hasher)
    }
}

impl<T: fmt::Debug> fmt::Debug for Array<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &**self)
    }
}

unsafe impl<T: Trace> Trace for Array<T> {
    impl_trace! { self, gc,
        for x in self {
            mark(x, gc);
        }
    }
}

impl<T> Array<T> {
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// Initializes an Array.
    /// To be safe it is required that the iterators length is known and exactly the same as the
    /// length of the allocated array.
    pub unsafe fn initialize<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        let iter = iterable.into_iter();
        self.len = iter
            .size_hint()
            .1
            .expect("initialize expected a known length");
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_values_offset() {
        use std::mem;
        use std::ptr;

        unsafe {
            let p: *const Array<i32> = ptr::null();
            assert_eq!(p as *const u8, &(*p).len as *const _ as *const u8);
            assert_eq!(
                (p as *const u8).offset(mem::size_of::<usize>() as isize),
                &(*p).array_start as *const _ as *const u8
            );
        }
    }
}
