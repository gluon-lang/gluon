use crate::real_std::{any::Any, fmt, marker::PhantomData, sync::Mutex};

use futures::{
    future::{self, Either, Shared},
    sync::oneshot,
    Future,
};

use crate::{
    api::{
        generic::A, FunctionRef, Getable, OpaqueValue, Pushable, Pushed, Userdata, VmType, WithVM,
    },
    base::types::{self, ArcType},
    gc::{Gc, GcPtr, Move, Traverseable},
    thread::{RootedThread, ThreadInternal},
    value::{Cloner, Value},
    vm::Thread,
    Error, ExternModule, Result, Variants,
};

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
        let alias = env.find_type_info("std.lazy.Lazy").unwrap().into_type();
        types::Type::app(alias, collect![T::make_type(vm)])
    }
}

fn force(
    WithVM { vm, value: lazy }: WithVM<&Lazy<A>>,
) -> impl Future<Item = Pushed<A>, Error = Error> {
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
                FunctionRef::<fn(()) -> OpaqueValue<RootedThread, A>>::from_value(
                    vm,
                    Variants::new(&value),
                )
            };
            drop(lazy_lock);
            let vm = vm.root_thread();
            Either::B(Either::A(function.call_fast_async(()).then(
                move |result| match result {
                    Ok(value) => {
                        {
                            let value = match lazy.thread.deep_clone_value(&vm, value.get_variant())
                            {
                                Ok(value) => value,
                                Err(err) => return Err(err.to_string().into()),
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
                        value.push(&mut vm.current_context()).unwrap();
                        Ok(Pushed::default())
                    }
                    Err(err) => Err(format!("{}", err).into()),
                },
            )))
        }
        None => match *lazy_lock {
            Lazy_::Blackhole(ref evaluating_thread, _)
                if *evaluating_thread == vm as *const Thread as usize =>
            {
                Either::A(future::err("<<loop>>".to_string().into()))
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
                Either::B(Either::B(
                    ready
                        .map_err(|_| {
                            panic!("Lazy: Sender where dropped before sending that the lazy value were evaluated")
                        })
                        .map(move |_| {
                            let lazy_lock = lazy.value.lock().unwrap();
                            match *lazy_lock {
                                Lazy_::Value(ref value) =>  {
                                    vm.current_context().push(value.clone());
                                    Pushed::default()
                                }
                                _ => unreachable!()
                            }
                        }),
                ))
            }
            Lazy_::Value(ref value) => {
                vm.current_context().push(value.clone());
                Either::A(future::ok(Pushed::default()))
            }
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
    pub use crate::lazy;
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    use self::std;

    ExternModule::new(
        vm,
        record! {
            type std::lazy::Lazy a => Lazy<A>,
            lazy => primitive!(1, std::lazy::lazy),
            force => primitive!(1, async fn std::lazy::force)
        },
    )
}
