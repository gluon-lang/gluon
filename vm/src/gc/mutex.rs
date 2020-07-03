use std::{
    fmt,
    ops::{Deref, DerefMut},
    sync,
};

use crate::gc::{Gc, Trace};

pub use std::sync::{PoisonError, TryLockError};

pub type TryLockResult<Guard> = Result<Guard, TryLockError<Guard>>;
pub type LockResult<Guard> = Result<Guard, PoisonError<Guard>>;

pub struct Mutex<T>
where
    T: ?Sized,
{
    // TODO Implement using atomics?
    // `rooted` is always locked first to avoid dead locks
    rooted: sync::Mutex<bool>,
    mutex: sync::Mutex<T>,
}

impl<T> Default for Mutex<T>
where
    T: Default,
{
    fn default() -> Self {
        Mutex::new(Default::default())
    }
}

impl<T> fmt::Debug for Mutex<T>
where
    T: ?Sized + fmt::Debug + Trace,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_lock() {
            Ok(guard) => f.debug_struct("Mutex").field("data", &&*guard).finish(),
            Err(TryLockError::Poisoned(err)) => f
                .debug_struct("Mutex")
                .field("data", &&**err.get_ref())
                .finish(),
            Err(TryLockError::WouldBlock) => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("Mutex")
                    .field("data", &LockedPlaceholder)
                    .finish()
            }
        }
    }
}

impl<T> Mutex<T> {
    pub fn new(value: T) -> Self {
        Mutex {
            rooted: sync::Mutex::new(true),
            mutex: sync::Mutex::new(value),
        }
    }
}

impl<T> Mutex<T>
where
    T: ?Sized + Trace,
{
    pub fn lock(&self) -> LockResult<MutexGuard<T>> {
        let rooted = self.rooted.lock().unwrap();
        match self.mutex.lock() {
            Ok(lock) => Ok(self.new_guard(*rooted, lock)),
            Err(err) => {
                let lock = err.into_inner();
                Err(PoisonError::new(self.new_guard(*rooted, lock)))
            }
        }
    }

    pub fn try_lock(&self) -> TryLockResult<MutexGuard<T>> {
        let rooted = self.rooted.lock().unwrap();
        match self.mutex.try_lock() {
            Ok(lock) => Ok(self.new_guard(*rooted, lock)),
            Err(sync::TryLockError::Poisoned(err)) => {
                let lock = err.into_inner();
                Err(TryLockError::Poisoned(PoisonError::new(
                    self.new_guard(*rooted, lock),
                )))
            }
            Err(sync::TryLockError::WouldBlock) => Err(sync::TryLockError::WouldBlock),
        }
    }

    pub fn is_poisoned(&self) -> bool {
        self.mutex.is_poisoned()
    }

    pub fn into_inner(self) -> LockResult<T>
    where
        T: Sized,
    {
        self.mutex.into_inner()
    }

    pub fn get_mut(&mut self) -> LockResult<&mut T> {
        self.mutex.get_mut()
    }

    fn new_guard<'a>(
        &'a self,
        rooted: bool,
        mut value: sync::MutexGuard<'a, T>,
    ) -> MutexGuard<'a, T> {
        if !rooted {
            unsafe {
                value.root();
            }
        }
        MutexGuard {
            value,
            rooted: &self.rooted,
        }
    }
}

unsafe impl<T> Trace for Mutex<T>
where
    T: Trace,
{
    unsafe fn root(&mut self) {
        let mut rooted = self.rooted.lock().unwrap();
        assert!(!*rooted, "Mutex can't be rooted twice!");
        *rooted = true;
        match self.mutex.try_lock() {
            Ok(mut lock) => lock.root(),
            Err(TryLockError::WouldBlock) => (), // The value will be rooted when the lock is released
            Err(TryLockError::Poisoned(err)) => err.into_inner().root(),
        }
    }
    unsafe fn unroot(&mut self) {
        let mut rooted = self.rooted.lock().unwrap();
        assert!(*rooted, "Mutex can't be unrooted twice!");
        *rooted = false;
        match self.mutex.try_lock() {
            Ok(mut lock) => lock.unroot(),
            Err(TryLockError::WouldBlock) => (), // The value will be unrooted when the lock is released
            Err(TryLockError::Poisoned(err)) => err.into_inner().unroot(),
        }
    }
    fn trace(&self, gc: &mut Gc) {
        match self.mutex.try_lock() {
            Ok(lock) => lock.trace(gc),
            Err(TryLockError::WouldBlock) => (), // The value is already rooted so we don't need to do anything here
            Err(TryLockError::Poisoned(err)) => err.into_inner().trace(gc),
        }
    }
}
pub struct MutexGuard<'a, T>
where
    T: ?Sized + Trace,
{
    rooted: &'a sync::Mutex<bool>,
    value: sync::MutexGuard<'a, T>,
}

impl<'a, T> Drop for MutexGuard<'a, T>
where
    T: ?Sized + Trace,
{
    fn drop(&mut self) {
        let rooted = self.rooted.lock().unwrap();
        if !*rooted {
            unsafe {
                self.value.unroot();
            }
        }
    }
}

impl<'a, T> Deref for MutexGuard<'a, T>
where
    T: ?Sized + Trace,
{
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'a, T> DerefMut for MutexGuard<'a, T>
where
    T: ?Sized + Trace,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::cell::Cell;

    struct Rooted<'a>(&'a Cell<bool>);

    unsafe impl<'a> Trace for Rooted<'a> {
        unsafe fn root(&mut self) {
            assert!(!self.0.get());
            self.0.set(true);
        }
        unsafe fn unroot(&mut self) {
            assert!(self.0.get());
            self.0.set(false);
        }
        fn trace(&self, _gc: &mut Gc) {}
    }

    #[test]
    fn rooted() {
        let rooted = Cell::new(true);
        let mutex = Mutex::new(Rooted(&rooted));

        assert!(rooted.get());
        {
            let _lock = mutex.lock().unwrap();
            assert!(rooted.get());
        }
        assert!(rooted.get());
    }

    #[test]
    fn unrooted() {
        let rooted = Cell::new(true);
        let mut mutex = Mutex::new(Rooted(&rooted));
        // Emulate this `Mutex` being unrooted (stored in another root)
        unsafe {
            mutex.unroot();
        }

        assert!(!rooted.get());
        {
            let _lock = mutex.lock().unwrap();
            assert!(rooted.get());
        }
        assert!(!rooted.get());
    }
}
