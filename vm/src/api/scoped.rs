use std::{fmt, ops::Deref, ptr::NonNull};

use std::sync::RwLock;

use base::types::ArcType;

use crate::{
    api::{Opaque, OpaqueValue, Pushable, VmType},
    gc::{Gc, Traverseable},
    thread::{ActiveThread, RootedThread, Thread, ThreadInternal},
    value::Userdata,
    Result,
};

pub struct Ref<'a, T>
where
    T: Userdata,
{
    reference: &'a T,
    gluon_reference: Option<RefGuard<T>>,
}

impl<'a, 'b, T> VmType for &'b mut Ref<'a, T>
where
    T: Userdata + VmType,
{
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'a, 'b, T> Pushable<'vm> for &'b mut Ref<'a, T>
where
    T: VmType + Userdata,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        Scoped::<T>::new(self.reference).push(context)?;
        let value = context.last().unwrap();
        self.gluon_reference = Some(RefGuard {
            gluon_reference: Opaque::from_value(context.thread().root_value(value)),
        });
        Ok(())
    }
}

impl<'a, T> Ref<'a, T>
where
    T: Userdata,
{
    pub fn new(reference: &'a T) -> Self {
        Ref {
            reference,
            gluon_reference: None,
        }
    }
}

pub struct RefGuard<T>
where
    T: Userdata,
{
    gluon_reference: OpaqueValue<RootedThread, Scoped<T>>,
}

impl<T> Drop for RefGuard<T>
where
    T: Userdata,
{
    fn drop(&mut self) {
        Scoped::invalidate(&*self.gluon_reference);
    }
}

pub(crate) struct Scoped<T: ?Sized> {
    ptr: RwLock<Option<NonNull<T>>>,
}

unsafe impl<T> Send for Scoped<T> where T: Send + Sync + ?Sized {}
unsafe impl<T> Sync for Scoped<T> where T: Send + Sync + ?Sized {}

impl<T> fmt::Debug for Scoped<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Scoped")
    }
}

impl<T> Scoped<T> {
    pub fn new(ptr: &T) -> Self {
        Scoped {
            ptr: RwLock::new(NonNull::new(ptr as *const T as *mut T)),
        }
    }

    pub fn read(&self) -> Result<ReadGuard<T>> {
        let ptr = self.ptr.read().unwrap();
        if let None = *ptr {
            return Err("Scoped pointer is invalidated".to_string().into());
        }
        Ok(ReadGuard(ptr))
    }

    pub fn invalidate(&self) {
        *self.ptr.write().unwrap() = None;
    }
}

impl<'vm, T: VmType> VmType for Scoped<T> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<T> Traverseable for Scoped<T>
where
    T: Traverseable,
{
    fn traverse(&self, gc: &mut Gc) {
        unsafe {
            if let Some(v) = *self.ptr.read().unwrap() {
                v.as_ref().traverse(gc);
            }
        }
    }
}

impl<T> Userdata for Scoped<T> where T: Userdata {}

#[doc(hidden)]
pub struct ReadGuard<'a, T>(std::sync::RwLockReadGuard<'a, Option<NonNull<T>>>);

impl<'a, T> Deref for ReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            match *self.0 {
                Some(v) => &*v.as_ptr(),
                None => panic!("Scoped pointer is invalidated"),
            }
        }
    }
}
