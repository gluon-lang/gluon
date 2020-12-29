use crate::real_std::{
    any::Any,
    collections::VecDeque,
    fmt,
    marker::PhantomData,
    slice,
    sync::{Arc, Mutex},
    time::Duration,
};

use futures::{
    future::{self, Either},
    prelude::*,
    task::Poll,
    try_join,
};

use crate::base::{
    kind::Kind,
    types::{ArcType, KindedIdent, Type},
};

use crate::{
    api::{
        generic::{A, B},
        Function, FunctionRef, Generic, Getable, OpaqueRef, OpaqueValue, OwnedFunction, Pushable,
        Pushed, RuntimeResult, Unrooted, VmType, WithVM, IO,
    },
    gc::{self, CloneUnrooted, GcPtr, Trace},
    stack::{ClosureState, ExternState, State},
    thread::{ActiveThread, ThreadInternal},
    types::VmInt,
    value::{Callable, Userdata, Value, ValueRepr},
    vm::{RootedThread, Thread},
    Error, ExternModule, Result as VmResult, Variants,
};

pub struct Sender<T> {
    // No need to traverse this thread reference as any thread having a reference to this `Sender`
    // would also directly own a reference to the `Thread`
    thread: GcPtr<Thread>,
    queue: Arc<Mutex<VecDeque<Value>>>,
    _element_type: PhantomData<T>,
}

impl<T> Userdata for Sender<T> where T: Any + Send + Sync + fmt::Debug {}

impl<T> fmt::Debug for Sender<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.queue.lock().unwrap())
    }
}

unsafe impl<T> Trace for Sender<T> {
    impl_trace! { self, _gc,
        // No need to traverse in Sender as values can only be accessed through Receiver
        {}
    }
}

impl<T> Sender<T> {
    fn send(&self, value: &Value) {
        // SAFETY Rooted when stored in `queue`
        unsafe {
            self.queue.lock().unwrap().push_back(value.clone_unrooted());
        }
    }
}

unsafe impl<T> Trace for Receiver<T> {
    impl_trace_fields! { self, gc; queue }
}

pub struct Receiver<T> {
    queue: Arc<Mutex<VecDeque<Value>>>,
    _element_type: PhantomData<T>,
}

impl<T> Userdata for Receiver<T> where T: Any + Send + Sync + fmt::Debug {}

impl<T> fmt::Debug for Receiver<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.queue.lock().unwrap())
    }
}

impl<T> Receiver<T> {
    fn try_recv(&self) -> Result<Value, ()> {
        self.queue.lock().unwrap().pop_front().ok_or(())
    }
}

impl<T: VmType> VmType for Sender<T>
where
    T::Type: Sized,
{
    type Type = Sender<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let env = vm.get_env();
        let symbol = env
            .find_type_info("std.channel.Sender")
            .unwrap()
            .name
            .clone();

        let k = vm.global_env().type_cache().kind_cache.typ();
        Type::app(
            Type::ident(KindedIdent {
                name: symbol,
                typ: Kind::function(k.clone(), k),
            }),
            collect![T::make_type(vm)],
        )
    }
}

impl<T: VmType> VmType for Receiver<T>
where
    T::Type: Sized,
{
    type Type = Receiver<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let symbol = vm
            .get_env()
            .find_type_info("std.channel.Receiver")
            .unwrap()
            .name
            .clone();
        let k = vm.global_env().type_cache().kind_cache.typ();
        Type::app(
            Type::ident(KindedIdent {
                name: symbol,
                typ: Kind::function(k.clone(), k),
            }),
            collect![T::make_type(vm)],
        )
    }
}

field_decl! { sender, receiver }

pub type ChannelRecord<S, R> = record_type!(sender => S, receiver => R);

/// FIXME The dummy `a` argument should not be needed to ensure that the channel can only be used
/// with a single type
fn channel(WithVM { vm, .. }: WithVM<Generic<A>>) -> IO<ChannelRecord<Sender<A>, Receiver<A>>> {
    let sender = Sender {
        thread: unsafe { GcPtr::from_raw(vm) },
        queue: Arc::new(Mutex::new(VecDeque::new())),
        _element_type: PhantomData,
    };
    let receiver = Receiver {
        queue: sender.queue.clone(),
        _element_type: PhantomData,
    };
    IO::Value(record_no_decl!(sender => sender, receiver => receiver))
}

fn recv(receiver: &Receiver<A>) -> IO<Result<Unrooted<A>, ()>> {
    IO::Value(receiver.try_recv().map_err(|_| ()).map(Unrooted::from))
}

fn send(sender: &Sender<A>, value: Generic<A>) -> IO<Result<(), ()>> {
    let value = match sender
        .thread
        .deep_clone_value(&sender.thread, value.get_value())
    {
        Ok(value) => value,
        Err(_) => return IO::Value(Err(())),
    };
    IO::Value(Ok(sender.send(value.get_value())))
}

async fn resume(child: RootedThread) -> IO<Result<(), String>> {
    let result = future::lazy(|cx| child.resume(cx)).await;
    match result {
        Poll::Pending => IO::Value(Ok(())),
        Poll::Ready(result) => match result {
            Ok(_) => IO::Value(Ok(())),
            Err(Error::Dead) => IO::Value(Err("Attempted to resume a dead thread".into())),
            Err(err) => {
                let fmt = format!("{}", err);
                IO::Exception(fmt)
            }
        },
    }
}

async fn yield_(_: ()) {
    let mut first = true;
    future::poll_fn(|cx| {
        if first {
            cx.waker().wake_by_ref();
            first = false;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    })
    .await
}

fn spawn<'vm>(value: WithVM<'vm, Function<&'vm Thread, IO<()>>>) -> IO<RootedThread> {
    spawn_(value).into()
}
fn spawn_<'vm>(value: WithVM<'vm, Function<&'vm Thread, IO<()>>>) -> VmResult<RootedThread> {
    let thread = value.vm.new_thread()?;
    {
        let mut context = thread.current_context();
        let value_variant = value.value.get_variant();
        let (callable, args) = match value_variant.get_repr() {
            ValueRepr::Closure(closure) => {
                value_variant.clone().vm_push(&mut context)?;
                (
                    construct_gc!(State::Closure(@ construct_gc!(ClosureState {
                        @ closure,
                        instruction_index: 0,
                    }))),
                    &[][..],
                )
            }
            ValueRepr::Function(function) => {
                value_variant.clone().vm_push(&mut context)?;
                (
                    construct_gc!(State::Extern(@ ExternState::new(function))),
                    &[][..],
                )
            }
            ValueRepr::PartialApplication(function) => (
                match &function.function {
                    Callable::Closure(closure) => {
                        context.push(construct_gc!(ValueRepr::Closure(@closure)));
                        construct_gc!(State::Closure(@ construct_gc!(ClosureState {
                            @ closure,
                            instruction_index: 0,
                        })))
                    }

                    Callable::Extern(function) => {
                        context.push(construct_gc!(ValueRepr::Function(@function)));
                        construct_gc!(State::Extern(@ ExternState::new(function)))
                    }
                },
                &function.args[..],
            ),
            _ => {
                value_variant.clone().vm_push(&mut context)?;
                (gc::Borrow::from_static(State::Unknown), &[][..])
            }
        };
        for a in args {
            context.push(a);
        }
        context.push(ValueRepr::Int(0));
        context
            .context()
            .stack
            .enter_scope(1 + args.len() as u32, &*callable)?;
    }
    Ok(thread)
}

type Action<T> = fn() -> IO<OpaqueValue<RootedThread, Pushed<T>>>;

#[cfg(target_arch = "wasm32")]
fn spawn_on<'vm>(
    _thread: RootedThread,
    _action: WithVM<'vm, FunctionRef<Action<A>>>,
) -> IO<OpaqueValue<&'vm Thread, IO<A>>> {
    IO::Exception("spawn_on requires the `tokio` crate".to_string())
}

#[cfg(not(target_arch = "wasm32"))]
fn spawn_on<'vm>(
    thread: RootedThread,
    action: WithVM<'vm, FunctionRef<Action<A>>>,
) -> IO<Pushed<IO<A>>> {
    struct SpawnFuture<F>(future::Shared<F>)
    where
        F: Future;

    impl<F> fmt::Debug for SpawnFuture<F>
    where
        F: Future,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "Future")
        }
    }

    impl<F> Userdata for SpawnFuture<F>
    where
        F: Future + Send + 'static,
        F::Output: Send + Sync,
    {
    }

    unsafe impl<F> Trace for SpawnFuture<F>
    where
        F: Future,
    {
        impl_trace! { self, _gc, { } }
    }

    impl<F> VmType for SpawnFuture<F>
    where
        F: Future,
        F::Output: VmType,
    {
        type Type = <F::Output as VmType>::Type;
    }

    fn push_future_wrapper<G>(context: &mut ActiveThread, _: &G)
    where
        G: Future<Output = IO<OpaqueValue<RootedThread, Pushed<A>>>> + Send + 'static,
    {
        fn future_wrapper<F>(
            data: &SpawnFuture<F>,
        ) -> impl Future<Output = IO<OpaqueValue<RootedThread, Pushed<A>>>>
        where
            F: Future<Output = IO<OpaqueValue<RootedThread, Pushed<A>>>> + Send + 'static,
        {
            let future = data.0.clone();
            future
        }

        primitive!(1, "unknown", async fn future_wrapper::<G>,
            [G]
            [G: Future<Output = IO<OpaqueValue<RootedThread, Pushed<A>>, >>
                + Send
                + 'static,
            ]
        )
        .vm_push(context)
        .unwrap();
    }
    use crate::value::PartialApplicationDataDef;

    let WithVM { vm, value: action } = action;
    let mut action = OwnedFunction::<Action<A>>::from_value(&thread, action.get_variant());

    let future = async move {
        match action.call_async().await {
            Ok(io) => io,
            Err(err) => IO::Exception(err.to_string()),
        }
    };

    let mut context = vm.current_context();

    push_future_wrapper(&mut context, &future);

    SpawnFuture(future.shared()).vm_push(&mut context).unwrap();

    let mut context = context.context();
    let callable = match context.stack[context.stack.len() - 2].get_repr() {
        ValueRepr::Function(ext) => construct_gc!(Callable::Extern(@ ext)),
        _ => unreachable!(),
    };

    let fields = slice::from_ref(context.stack.last().unwrap());
    let def = construct_gc!(PartialApplicationDataDef(@callable, fields));
    let value = Variants::from(context.gc.alloc(def).unwrap());

    context.stack.pop_many(2);
    context.stack.push(value);

    IO::Value(Pushed::default())
}

fn join(
    WithVM { vm: vm_a, value: a }: WithVM<OpaqueRef<IO<A>>>,
    b: OpaqueRef<IO<B>>,
) -> impl Future<Output = RuntimeResult<IO<(Generic<A>, Generic<B>)>, Error>> {
    let vm_b = match vm_a.new_thread() {
        Ok(vm) => vm,
        Err(err) => return Either::Right(future::ready(RuntimeResult::Panic(err))),
    };

    let mut action_a: OwnedFunction<fn(()) -> OpaqueValue<RootedThread, A>> =
        Getable::from_value(&vm_a, a.get_variant());
    let mut action_b: OwnedFunction<fn(()) -> OpaqueValue<RootedThread, B>> =
        Getable::from_value(&vm_b, b.get_variant());

    Either::Left(async move {
        let result = try_join!(action_a.call_async(()), action_b.call_async(()));
        trace!("join done: {:?}", result);
        result.map(IO::Value).into()
    })
}

fn new_thread(WithVM { vm, .. }: WithVM<()>) -> IO<RootedThread> {
    match vm.new_thread() {
        Ok(thread) => IO::Value(thread),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn sleep(ms: VmInt) -> IO<()> {
    ::std::thread::sleep(Duration::from_millis(ms as u64));
    IO::Value(())
}

fn interrupt(thread: RootedThread) -> IO<()> {
    thread.interrupt();
    IO::Value(())
}

mod std {
    pub use crate::channel;
    pub mod thread {
        pub use crate::channel as prim;
    }
}

pub fn load_channel<'vm>(vm: &'vm Thread) -> VmResult<ExternModule> {
    let _ = vm.register_type::<Sender<A>>("std.channel.Sender", &["a"]);
    let _ = vm.register_type::<Receiver<A>>("std.channel.Receiver", &["a"]);

    ExternModule::new(
        vm,
        record! {
            type Sender a => Sender<A>,
            type Receiver a => Sender<A>,
            channel => primitive!(1, std::channel::channel),
            recv => primitive!(1, std::channel::recv),
            send => primitive!(2, std::channel::send),
        },
    )
}

pub fn load_thread<'vm>(vm: &'vm Thread) -> VmResult<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            resume => primitive!(1, async fn std::thread::prim::resume),
            (yield_ "yield") => primitive!(1, "std.thread.prim.yield", async fn std::thread::prim::yield_),
            spawn => primitive!(1, std::thread::prim::spawn),
            spawn_on => primitive!(2, std::thread::prim::spawn_on),
            new_thread => primitive!(1, std::thread::prim::new_thread),
            interrupt => primitive!(1, std::thread::prim::interrupt),
            sleep => primitive!(1, std::thread::prim::sleep),
            join => primitive!(2, async fn std::thread::prim::join),
        },
    )
}
