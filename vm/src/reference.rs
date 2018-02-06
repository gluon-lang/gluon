use std::any::Any;
use std::fmt;
use std::sync::Mutex;
use std::marker::PhantomData;

use base::types::{ArcType, Type};
use {ExternModule, Result};
use gc::{Gc, GcPtr, Move, Traverseable};
use vm::Thread;
use thread::ThreadInternal;
use value::{Cloner, Value};
use api::{Generic, RuntimeResult, Userdata, VmType, WithVM};
use api::generic::A;

pub struct Reference<T> {
    value: Mutex<Value>,
    thread: GcPtr<Thread>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Reference<T>
where
    T: Any + Send + Sync,
{
    fn deep_clone(&self, deep_cloner: &mut Cloner) -> Result<GcPtr<Box<Userdata>>> {
        let value = self.value.lock().unwrap();
        let cloned_value = deep_cloner.deep_clone(&value)?;
        let data: Box<Userdata> = Box::new(Reference {
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
    fn traverse(&self, gc: &mut Gc) {
        self.value.lock().unwrap().traverse(gc)
    }
}

impl<T> VmType for Reference<T>
where
    T: VmType,
    T::Type: Sized,
{
    type Type = Reference<T::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        let env = vm.global_env().get_env();
        let symbol = env.find_type_info("Ref").unwrap().name.clone();
        let ctor = Type::ident(symbol);
        Type::app(ctor, collect![T::make_type(vm)])
    }
}

fn set(r: &Reference<A>, a: Generic<A>) -> RuntimeResult<(), String> {
    unsafe {
        match r.thread.deep_clone_value(&r.thread, a.get_value()) {
            Ok(a) => {
                *r.value.lock().unwrap() = a;
                RuntimeResult::Return(())
            }
            Err(err) => RuntimeResult::Panic(format!("{}", err)),
        }
    }
}

fn get(r: &Reference<A>) -> Generic<A> {
    Generic::from(r.value.lock().unwrap().clone())
}

fn make_ref(a: WithVM<Generic<A>>) -> Reference<A> {
    unsafe {
        Reference {
            value: Mutex::new(a.value.get_value()),
            thread: GcPtr::from_raw(a.vm),
            _marker: PhantomData,
        }
    }
}

mod std {
    pub use reference;
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    use self::std;

    let _ = vm.register_type::<Reference<A>>("Ref", &["a"]);
    ExternModule::new(
        vm,
        record!{
            (store "<-") => named_primitive!(2, "std.reference.(<-)", std::reference::set),
            load => named_primitive!(1, "std.reference.load", std::reference::get),
            (ref_ "ref") =>  named_primitive!(1, "std.reference.ref", std::reference::make_ref),
        },
    )
}
