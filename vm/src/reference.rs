use crate::real_std::{any::Any, fmt, marker::PhantomData, sync::Mutex};

use crate::{
    api::{generic::A, Generic, RuntimeResult, Unrooted, Userdata, WithVM},
    gc::{GcPtr, Move, Traverseable},
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
    fn deep_clone(&self, deep_cloner: &mut Cloner) -> Result<GcPtr<Box<dyn Userdata>>> {
        let value = self.value.lock().unwrap();
        let cloned_value = deep_cloner.deep_clone(&value)?;
        let data: Box<dyn Userdata> = Box::new(Reference {
            value: Mutex::new(cloned_value),
            thread: unsafe { GcPtr::from_raw(deep_cloner.thread()) },
            _marker: PhantomData::<A>,
        });
        deep_cloner.gc().alloc(Move(data))
    }
}

impl<T> fmt::Debug for Reference<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Ref({:?})", *self.value.lock().unwrap())
    }
}

impl<T> Traverseable for Reference<T> {
    impl_traverseable! { self, gc,
        mark(&*self.value.lock().unwrap(), gc)
    }
}

fn set(r: &Reference<A>, a: Generic<A>) -> RuntimeResult<(), String> {
    match r.thread.deep_clone_value(&r.thread, a.get_variant()) {
        Ok(a) => {
            *r.value.lock().unwrap() = a;
            RuntimeResult::Return(())
        }
        Err(err) => RuntimeResult::Panic(format!("{}", err)),
    }
}

fn get(r: &Reference<A>) -> Unrooted<A> {
    Unrooted::from(r.value.lock().unwrap().clone())
}

fn make_ref(a: WithVM<Generic<A>>) -> Reference<A> {
    unsafe {
        Reference {
            value: Mutex::new(a.value.get_variant().get_value()),
            thread: GcPtr::from_raw(a.vm),
            _marker: PhantomData,
        }
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
