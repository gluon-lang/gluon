use std::{
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use std::sync::RwLock;

use base::types::ArcType;

use crate::{
    api::{Opaque, OpaqueValue, Pushable, VmType},
    gc::{Gc, Trace},
    thread::{ActiveThread, RootedThread, Thread, ThreadInternal},
    value::Userdata,
    Result,
};

pub struct Ref<'a, T>
where
    T: Userdata,
{
    reference: &'a T,
    gluon_reference: Option<RefGuard<T, &'static ()>>,
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        Scoped::<T, _>::new(self.reference).vm_push(context)?;
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

pub struct RefMut<'a, T>
where
    T: Userdata,
{
    reference: &'a mut T,
    gluon_reference: Option<RefGuard<T, &'static mut ()>>,
}

impl<'a, 'b, T> VmType for &'b mut RefMut<'a, T>
where
    T: Userdata + VmType,
{
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'a, 'b, T> Pushable<'vm> for &'b mut RefMut<'a, T>
where
    T: VmType + Userdata,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        Scoped::<T, _>::new_mut(self.reference).vm_push(context)?;
        let value = context.last().unwrap();
        self.gluon_reference = Some(RefGuard {
            gluon_reference: Opaque::from_value(context.thread().root_value(value)),
        });
        Ok(())
    }
}

impl<'a, T> RefMut<'a, T>
where
    T: Userdata,
{
    pub fn new(reference: &'a mut T) -> Self {
        RefMut {
            reference,
            gluon_reference: None,
        }
    }
}

struct RefGuard<T, M>
where
    T: Userdata,
    M: 'static,
{
    gluon_reference: OpaqueValue<RootedThread, Scoped<T, M>>,
}

impl<T, M> Drop for RefGuard<T, M>
where
    T: Userdata,
    M: 'static,
{
    fn drop(&mut self) {
        Scoped::invalidate(&*self.gluon_reference);
    }
}

pub(crate) struct Scoped<T: ?Sized, M> {
    ptr: RwLock<Option<NonNull<T>>>,
    _marker: PhantomData<M>,
}

unsafe impl<T, M> Send for Scoped<T, M> where T: Send + Sync + ?Sized {}
unsafe impl<T, M> Sync for Scoped<T, M> where T: Send + Sync + ?Sized {}

impl<T, M> fmt::Debug for Scoped<T, M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Scoped")
    }
}

impl<T> Scoped<T, &'static ()> {
    pub fn new(ptr: &T) -> Self {
        Scoped {
            ptr: RwLock::new(NonNull::new(ptr as *const T as *mut T)),
            _marker: PhantomData,
        }
    }
}

impl<T> Scoped<T, &'static mut ()> {
    pub fn new_mut(ptr: &mut T) -> Self {
        Scoped {
            ptr: RwLock::new(NonNull::new(ptr as *mut T)),
            _marker: PhantomData,
        }
    }

    pub fn write(&self) -> Result<WriteGuard<T>> {
        let ptr = self.ptr.write().unwrap();
        if let None = *ptr {
            return Err("Scoped pointer is invalidated".to_string().into());
        }
        Ok(WriteGuard(ptr))
    }
}

impl<T, M> Scoped<T, M> {
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

impl<'vm, T: VmType, M> VmType for Scoped<T, M> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

unsafe impl<T, M> Trace for Scoped<T, M>
where
    T: Trace,
{
    fn trace(&self, gc: &mut Gc) {
        if let Some(v) = *self.ptr.read().unwrap() {
            unsafe {
                v.as_ref().trace(gc);
            }
        }
    }
}

impl<T, M> Userdata for Scoped<T, M>
where
    T: Userdata,
    M: 'static,
{
}

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

#[doc(hidden)]
pub struct WriteGuard<'a, T>(std::sync::RwLockWriteGuard<'a, Option<NonNull<T>>>);

impl<'a, T> Deref for WriteGuard<'a, T> {
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

impl<'a, T> DerefMut for WriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            match *self.0 {
                Some(v) => &mut *v.as_ptr(),
                None => panic!("Scoped pointer is invalidated"),
            }
        }
    }
}
