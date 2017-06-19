use std::any::Any;
use std::borrow::Cow;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Mutex;

use base::types;
use base::types::{Type, ArcType};
use gc::{Gc, GcPtr, Move, Traverseable};
use api::{FunctionRef, Getable, OpaqueValue, Userdata, VmType, WithVM, RuntimeResult};
use api::Generic;
use api::generic::A;
use vm::Thread;
use {Error, Result, Variants};
use value::{Cloner, Value};
use thread::ThreadInternal;

pub struct Lazy<T> {
    value: Mutex<Lazy_>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Lazy<T>
where
    T: Any + Send + Sync,
{
    fn deep_clone(&self, deep_cloner: &mut Cloner) -> Result<GcPtr<Box<Userdata>>> {
        let value = self.value.lock().unwrap();
        let cloned_value = match *value {
            Lazy_::Blackhole => return Err(Error::Message("<<loop>>".into())),
            Lazy_::Thunk(value) => Lazy_::Thunk(deep_cloner.deep_clone(value)?),
            Lazy_::Value(value) => Lazy_::Value(deep_cloner.deep_clone(value)?),
        };
        let data: Box<Userdata> = Box::new(Lazy {
            value: Mutex::new(cloned_value),
            _marker: PhantomData::<A>,
        });
        deep_cloner.gc().alloc(Move(data))
    }
}

impl<T> fmt::Debug for Lazy<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lazy({:?})", *self.value.lock().unwrap())
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Lazy_ {
    Blackhole,
    Thunk(Value),
    Value(Value),
}

impl<T> Traverseable for Lazy<T> {
    fn traverse(&self, gc: &mut Gc) {
        match *self.value.lock().unwrap() {
            Lazy_::Blackhole => (),
            Lazy_::Thunk(value) => value.traverse(gc),
            Lazy_::Value(value) => value.traverse(gc),
        }
    }
}

impl<T> VmType for Lazy<T>
where
    T: VmType,
    T::Type: Sized,
{
    type Type = Lazy<T::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        let env = vm.global_env().get_env();
        let symbol = env.find_type_info("Lazy").unwrap().name.clone();
        let ctor = Type::ident(symbol);
        types::Type::app(ctor, collect![T::make_type(vm)])
    }
}

fn force(
    WithVM { vm, value: lazy }: WithVM<&Lazy<A>>,
) -> RuntimeResult<Generic<A>, Cow<'static, str>> {
    let mut lazy_lock = lazy.value.lock().unwrap();
    match *lazy_lock {
        Lazy_::Blackhole => RuntimeResult::Panic("<<loop>>".into()),
        Lazy_::Thunk(value) => {
            *lazy_lock = Lazy_::Blackhole;
            let mut function = unsafe {
                FunctionRef::<fn(()) -> Generic<A>>::from_value(vm, Variants::new(&value)).unwrap()
            };
            drop(lazy_lock);
            match function.call(()) {
                Ok(value) => {
                    *lazy.value.lock().unwrap() = Lazy_::Value(value.0);
                    RuntimeResult::Return(value)
                }
                Err(err) => RuntimeResult::Panic(format!("{}", err).into()),
            }
        }
        Lazy_::Value(value) => RuntimeResult::Return(Generic::from(value)),
    }
}

fn lazy(f: OpaqueValue<&Thread, fn(()) -> A>) -> Lazy<A> {
    unsafe {
        Lazy {
            value: Mutex::new(Lazy_::Thunk(f.get_value())),
            _marker: PhantomData,
        }
    }
}

pub fn load<'vm>(vm: &'vm Thread) -> Result<()> {
    vm.define_global("lazy", primitive!(1 lazy))?;
    vm.define_global("force", primitive!(1 force))?;
    Ok(())
}
