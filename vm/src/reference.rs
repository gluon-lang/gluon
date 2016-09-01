use std::any::Any;
use std::fmt;
use std::sync::Mutex;
use std::marker::PhantomData;

use base::types::{Type, TcType};
use Result;
use gc::{Gc, GcPtr, Traverseable};
use vm::Thread;
use thread::ThreadInternal;
use value::Value;
use api::{MaybeError, Generic, Userdata, VmType, WithVM};
use api::generic::A;

struct Reference<T> {
    value: Mutex<Value>,
    thread: GcPtr<Thread>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Reference<T> where T: Any + Send + Sync {}

impl<T> fmt::Debug for Reference<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.value.lock().unwrap())
    }
}

impl<T> Traverseable for Reference<T> {
    fn traverse(&self, gc: &mut Gc) {
        self.value.lock().unwrap().traverse(gc)
    }
}

impl<T> VmType for Reference<T>
    where T: VmType,
          T::Type: Sized
{
    type Type = Reference<T::Type>;

    fn make_type(vm: &Thread) -> TcType {
        let env = vm.global_env().get_env();
        let symbol = env.find_type_info("Ref").unwrap().name.clone();
        let ctor = Type::ident(symbol);
        Type::app(ctor, vec![T::make_type(vm)])
    }
}

fn set(r: &Reference<A>, a: Generic<A>) -> MaybeError<(), String> {
    match r.thread.deep_clone(a.0) {
        Ok(a) => {
            *r.value.lock().unwrap() = a;
            MaybeError::Ok(())
        }
        Err(err) => MaybeError::Err(format!("{}", err)),
    }
}

fn get(r: &Reference<A>) -> Generic<A> {
    Generic::from(*r.value.lock().unwrap())
}

fn make_ref(a: WithVM<Generic<A>>) -> Reference<A> {
    Reference {
        value: Mutex::new(a.value.0),
        thread: unsafe { GcPtr::from_raw(a.vm) },
        _marker: PhantomData,
    }
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}

pub fn load(vm: &Thread) -> Result<()> {
    let _ = vm.register_type::<Reference<A>>("Ref", &["a"]);
    try!(vm.define_global("<-", f2(set)));
    try!(vm.define_global("load", f1(get)));
    try!(vm.define_global("ref", f1(make_ref)));
    Ok(())
}
