use std::any::Any;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Mutex;

use futures::Future;
use futures::future::Shared;
use futures::sync::oneshot;

use base::types;
use base::types::{ArcType, Type};
use gc::{Gc, GcPtr, Move, Traverseable};
use api::{FunctionRef, Getable, OpaqueValue, PrimitiveFuture, Userdata, VmType, WithVM};
use future::FutureValue;
use api::Generic;
use api::generic::A;
use vm::Thread;
use {Error, ExternModule, Result, Variants};
use value::{Cloner, Value};
use thread::ThreadInternal;

pub struct Lazy<T> {
    value: Mutex<Lazy_>,
    // No need to traverse this thread reference as any thread having a reference to this `Sender`
    // would also directly own a reference to the `Thread`
    thread: GcPtr<Thread>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Lazy<T>
where
    T: Any + Send + Sync,
{
    fn deep_clone(&self, deep_cloner: &mut Cloner) -> Result<GcPtr<Box<Userdata>>> {
        let value = self.value.lock().unwrap();
        let cloned_value = match *value {
            Lazy_::Blackhole(..) => return Err(Error::Message("<<loop>>".into())),
            Lazy_::Thunk(ref value) => Lazy_::Thunk(deep_cloner.deep_clone(value)?),
            Lazy_::Value(ref value) => Lazy_::Value(deep_cloner.deep_clone(value)?),
        };
        let data: Box<Userdata> = Box::new(Lazy {
            value: Mutex::new(cloned_value),
            thread: unsafe { GcPtr::from_raw(deep_cloner.thread()) },
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

#[derive(Debug)]
enum Lazy_ {
    Blackhole(
        usize,
        Option<(oneshot::Sender<()>, Shared<oneshot::Receiver<()>>)>,
    ),
    Thunk(Value),
    Value(Value),
}

impl<T> Traverseable for Lazy<T> {
    fn traverse(&self, gc: &mut Gc) {
        match *self.value.lock().unwrap() {
            Lazy_::Blackhole(..) => (),
            Lazy_::Thunk(ref value) => value.traverse(gc),
            Lazy_::Value(ref value) => value.traverse(gc),
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

fn force(WithVM { vm, value: lazy }: WithVM<&Lazy<A>>) -> PrimitiveFuture<Generic<A>> {
    let mut lazy_lock = lazy.value.lock().unwrap();
    let lazy: GcPtr<Lazy<A>> = unsafe { GcPtr::from_raw(lazy) };
    let thunk = match *lazy_lock {
        Lazy_::Thunk(ref value) => Some(value.clone()),
        _ => None,
    };
    match thunk {
        Some(value) => {
            *lazy_lock = Lazy_::Blackhole(vm as *const Thread as usize, None);
            let mut function = unsafe {
                FunctionRef::<fn(()) -> Generic<A>>::from_value(vm, Variants::new(&value))
            };
            drop(lazy_lock);
            let vm = vm.root_thread();
            function
                .call_fast_async(())
                .then(move |result| match result {
                    Ok(value) => {
                        unsafe {
                            let value = match lazy.thread.deep_clone_value(&vm, value.get_value()) {
                                Ok(value) => value,
                                Err(err) => return FutureValue::sync(Err(err.to_string().into())),
                            };
                            let mut lazy_lock = lazy.value.lock().unwrap();
                            match *lazy_lock {
                                Lazy_::Blackhole(_, ref mut x) => {
                                    if let Some((sender, _receiver)) = x.take() {
                                        sender.send(()).unwrap();
                                    }
                                }
                                _ => unreachable!(),
                            }
                            *lazy_lock = Lazy_::Value(value);
                        }
                        FutureValue::sync(Ok(value))
                    }
                    Err(err) => FutureValue::sync(Err(format!("{}", err).into())),
                })
                .boxed()
        }
        None => match *lazy_lock {
            Lazy_::Blackhole(ref evaluating_thread, _)
                if *evaluating_thread == vm as *const Thread as usize =>
            {
                FutureValue::Value(Err("<<loop>>".to_string().into()))
            }
            Lazy_::Blackhole(_, ref mut opt) => {
                // The current thread was not the one that started evaluating the lazy value.
                // Store a oneshot future which that thread fires once the lazy value has been
                // evaluated
                if opt.is_none() {
                    let (tx, rx) = oneshot::channel();
                    *opt = Some((tx, rx.shared()));
                }
                let ready = opt.as_ref().unwrap().1.clone();
                let vm = vm.root_thread();
                FutureValue::Future(Box::new(
                    ready
                        .map_err(|_| {
                            panic!("Lazy: Sender where dropped before sending that the lazy value were evaluated")
                        })
                        .and_then(move |_| {
                            force(WithVM {
                                vm: &vm,
                                value: &*lazy,
                            })
                        }),
                ))
            }
            Lazy_::Value(ref value) => FutureValue::Value(Ok(Generic::from(value.clone()))),
            _ => unreachable!(),
        },
    }
}

fn lazy(f: OpaqueValue<&Thread, fn(()) -> A>) -> Lazy<A> {
    unsafe {
        Lazy {
            value: Mutex::new(Lazy_::Thunk(f.get_value())),
            thread: GcPtr::from_raw(f.vm()),
            _marker: PhantomData,
        }
    }
}

mod std {
    pub use lazy;
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    use self::std;

    ExternModule::new(
        vm,
        record!{
            lazy => primitive!(1 std::lazy::lazy),
            force => primitive!(1 std::lazy::force)
        },
    )
}
