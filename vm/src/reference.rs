use crate::real_std::{any::Any, fmt, marker::PhantomData, sync::Mutex};

use crate::{
    api::{generic::A, Generic, Unrooted, Userdata, WithVM, IO},
    gc::{CloneUnrooted, GcPtr, GcRef, Move, Trace},
    thread::ThreadInternal,
    value::{Cloner, Value},
    vm::Thread,
    ExternModule, Result,
};

#[derive(VmType)]
#[gluon(gluon_vm)]
#[gluon(vm_type = "std.reference.Reference")]
pub struct Reference<T> {
    value: Mutex<Value>,
    thread: GcPtr<Thread>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Reference<T>
where
    T: Any + Send + Sync,
{
    fn deep_clone<'gc>(
        &self,
        deep_cloner: &'gc mut Cloner,
    ) -> Result<GcRef<'gc, Box<dyn Userdata>>> {
        let value = self.value.lock().unwrap();
        // SAFETY During the `alloc` call the unrooted values are scanned through the `DataDef`
        unsafe {
            let cloned_value = deep_cloner.deep_clone(&value)?.unrooted();
            let data: Box<dyn Userdata> = Box::new(Reference {
                value: Mutex::new(cloned_value),
                thread: GcPtr::from_raw(deep_cloner.thread()),
                _marker: PhantomData::<A>,
            });
            deep_cloner.gc().alloc(Move(data))
        }
    }
}

impl<T> fmt::Debug for Reference<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ref({:?})", *self.value.lock().unwrap())
    }
}

unsafe impl<T> Trace for Reference<T> {
    impl_trace_fields! { self, gc; value }
}

fn set(r: &Reference<A>, a: Generic<A>) -> IO<()> {
    match r.thread.deep_clone_value(&r.thread, a.get_value()) {
        // SAFETY Rooted when stored in the reference
        Ok(a) => unsafe {
            *r.value.lock().unwrap() = a.get_value().clone_unrooted();
            IO::Value(())
        },
        Err(err) => IO::Exception(format!("{}", err)),
    }
}

fn get(r: &Reference<A>) -> IO<Unrooted<A>> {
    // SAFETY The returned, unrooted value gets pushed immediately to the stack
    IO::Value(unsafe { Unrooted::from(r.value.lock().unwrap().clone_unrooted()) })
}

fn make_ref(a: WithVM<Generic<A>>) -> IO<Reference<A>> {
    // SAFETY The returned, unrooted value gets pushed immediately to the stack
    unsafe {
        IO::Value(Reference {
            value: Mutex::new(a.value.get_value().clone_unrooted()),
            thread: GcPtr::from_raw(a.vm),
            _marker: PhantomData,
        })
    }
}

mod std {
    pub mod reference {
        pub use crate::reference as prim;
    }
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    let _ = vm.register_type::<Reference<A>>("std.reference.Reference", &["a"]);
    ExternModule::new(
        vm,
        record! {
            type Reference a => Reference<A>,
            (store "<-") => primitive!(2, "std.reference.prim.(<-)", std::reference::prim::set),
            load => primitive!(1, "std.reference.prim.load", std::reference::prim::get),
            (ref_ "ref") =>  primitive!(1, "std.reference.prim.ref", std::reference::prim::make_ref),
        },
    )
}

pub mod st {
    use super::*;

    use crate::api::RuntimeResult;

    fn set(r: &Reference<A>, a: Generic<A>) -> RuntimeResult<(), String> {
        match r.thread.deep_clone_value(&r.thread, a.get_value()) {
            // SAFETY Rooted when stored in the reference
            Ok(a) => unsafe {
                *r.value.lock().unwrap() = a.get_value().clone_unrooted();
                RuntimeResult::Return(())
            },
            Err(err) => RuntimeResult::Panic(format!("{}", err)),
        }
    }

    fn get(r: &Reference<A>) -> Unrooted<A> {
        // SAFETY The returned, unrooted value gets pushed immediately to the stack
        unsafe { Unrooted::from(r.value.lock().unwrap().clone_unrooted()) }
    }

    fn make_ref(a: WithVM<Generic<A>>) -> Reference<A> {
        // SAFETY The returned, unrooted value gets pushed immediately to the stack
        unsafe {
            Reference {
                value: Mutex::new(a.value.get_value().clone_unrooted()),
                thread: GcPtr::from_raw(a.vm),
                _marker: PhantomData,
            }
        }
    }

    mod std {
        pub mod st {
            pub mod reference {
                pub use crate::reference::st as prim;
            }
        }
    }

    pub fn load(vm: &Thread) -> Result<ExternModule> {
        ExternModule::new(
            vm,
            record! {
                type Reference a => Reference<A>,
                (store "<-") => primitive!(2, "std.st.reference.prim.(<-)", std::st::reference::prim::set),
                load => primitive!(1, "std.st.reference.prim.load", std::st::reference::prim::get),
                (ref_ "ref") =>  primitive!(1, "std.st.reference.prim.ref", std::st::reference::prim::make_ref),
            },
        )
    }
}
