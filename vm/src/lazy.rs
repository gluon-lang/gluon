use crate::real_std::{any::Any, fmt, marker::PhantomData, sync::Mutex};

use futures::{
    channel::oneshot,
    future::{self, Either, Shared},
    prelude::*,
    Future,
};

use crate::{
    api::{
        generic::A, Getable, OpaqueValue, OwnedFunction, Pushable, Pushed, RuntimeResult, Userdata,
        VmType, WithVM,
    },
    base::types::{self, ArcType},
    gc::{CloneUnrooted, GcPtr, GcRef, Move, Trace},
    thread::{RootedThread, ThreadInternal},
    value::{Cloner, Value},
    vm::Thread,
    Error, ExternModule, Result,
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
    fn deep_clone<'gc>(
        &self,
        deep_cloner: &'gc mut Cloner,
    ) -> Result<GcRef<'gc, Box<dyn Userdata>>> {
        let value = self.value.lock().unwrap();

        // SAFETY During the `alloc` call the unrooted values are scanned through the `DataDef`
        unsafe {
            let cloned_value = match *value {
                Lazy_::Blackhole(..) => return Err(Error::Message("<<loop>>".into())),
                Lazy_::Thunk(ref value) => Lazy_::Thunk(deep_cloner.deep_clone(value)?.unrooted()),
                Lazy_::Value(ref value) => Lazy_::Value(deep_cloner.deep_clone(value)?.unrooted()),
            };
            let data: Box<dyn Userdata> = Box::new(Lazy {
                value: Mutex::new(cloned_value),
                thread: GcPtr::from_raw(deep_cloner.thread()),
                _marker: PhantomData::<A>,
            });
            deep_cloner.gc().alloc(Move(data))
        }
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

unsafe impl<T> Trace for Lazy<T> {
    impl_trace! { self, gc,
        match &mut *self.value.lock().unwrap() {
            Lazy_::Blackhole(..) => (),
            Lazy_::Thunk(value) => mark(value, gc),
            Lazy_::Value(value) => mark(value, gc),
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
        let env = vm.get_env();
        let alias = env.find_type_info("std.lazy.Lazy").unwrap().into_type();
        types::Type::app(alias, collect![T::make_type(vm)])
    }
}

fn force(
    WithVM { vm, value: lazy }: WithVM<&Lazy<A>>,
) -> impl Future<Output = RuntimeResult<Pushed<A>, Error>> {
    let mut lazy_lock = lazy.value.lock().unwrap();
    let lazy: GcPtr<Lazy<A>> = unsafe { GcPtr::from_raw(lazy) };
    let thunk = match *lazy_lock {
        Lazy_::Thunk(ref value) => Some(value),
        _ => None,
    };
    match thunk {
        Some(value) => {
            let mut function = OwnedFunction::<fn(()) -> OpaqueValue<RootedThread, A>>::from_value(
                vm,
                value.get_variants(),
            );
            *lazy_lock = Lazy_::Blackhole(vm as *const Thread as usize, None);
            drop(lazy_lock);
            let vm = vm.root_thread();
            Either::Right(Either::Left(async move {
                match function.call_async(()).await {
                    Ok(value) => {
                        {
                            let value = match lazy.thread.deep_clone_value(&vm, value.get_value()) {
                                Ok(value) => value,
                                Err(err) => return RuntimeResult::Panic(err.to_string().into()),
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
                            // SAFETY Rooted by being stored in the lazy value
                            unsafe {
                                *lazy_lock = Lazy_::Value(value.get_variant().unrooted());
                            }
                        }
                        value.vm_push(&mut vm.current_context()).unwrap();
                        RuntimeResult::Return(Pushed::default())
                    }
                    Err(err) => RuntimeResult::Panic(format!("{}", err).into()),
                }
            }))
        }
        None => match *lazy_lock {
            Lazy_::Blackhole(ref evaluating_thread, _)
                if *evaluating_thread == vm as *const Thread as usize =>
            {
                Either::Left(future::ready(RuntimeResult::Panic(
                    "<<loop>>".to_string().into(),
                )))
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
                Either::Right(Either::Right(
                    ready
                        .map(move |_| {
                            let lazy_lock = lazy.value.lock().unwrap();
                            match *lazy_lock {
                                Lazy_::Value(ref value) => {
                                    vm.current_context().push(value.clone());
                                    Pushed::default()
                                }
                                _ => unreachable!(),
                            }
                        })
                        .map(RuntimeResult::Return),
                ))
            }
            Lazy_::Value(ref value) => {
                vm.current_context().push(value.clone());
                Either::Left(future::ready(RuntimeResult::Return(Pushed::default())))
            }
            _ => unreachable!(),
        },
    }
}

fn lazy(f: OpaqueValue<&Thread, fn(()) -> A>) -> Lazy<A> {
    // SAFETY We get rooted immediately on returning
    unsafe {
        Lazy {
            value: Mutex::new(Lazy_::Thunk(f.get_value().clone_unrooted())),
            thread: GcPtr::from_raw(f.vm()),
            _marker: PhantomData,
        }
    }
}

mod std {
    pub use crate::lazy;
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            type std::lazy::Lazy a => Lazy<A>,
            lazy => primitive!(1, std::lazy::lazy),
            force => primitive!(1, async fn std::lazy::force)
        },
    )
}
