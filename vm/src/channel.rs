use std::any::Any;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

use futures::Future;
use futures::sync::oneshot;

use base::types::{ArcType, Type};

use {Error, ExternModule, Result as VmResult};
use api::{primitive, AsyncPushable, Function, FunctionRef, FutureResult, Generic, Getable,
          OpaqueValue, OwnedFunction, Pushable, RuntimeResult, VmType, WithVM, IO};
use api::generic::A;
use gc::{Gc, GcPtr, Traverseable};
use vm::{RootedThread, Status, Thread};
use thread::{OwnedContext, ThreadInternal};
use value::{Callable, GcStr, Userdata, ValueRepr};
use stack::{StackFrame, State};
use types::VmInt;

pub struct Sender<T> {
    // No need to traverse this thread reference as any thread having a reference to this `Sender`
    // would also directly own a reference to the `Thread`
    thread: GcPtr<Thread>,
    queue: Arc<Mutex<VecDeque<T>>>,
}

impl<T> Userdata for Sender<T>
where
    T: Any + Send + Sync + fmt::Debug + Traverseable,
{
}

impl<T> fmt::Debug for Sender<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.queue.lock().unwrap())
    }
}

impl<T> Traverseable for Sender<T> {
    fn traverse(&self, _gc: &mut Gc) {
        // No need to traverse in Sender as values can only be accessed through Receiver
    }
}

impl<T> Sender<T> {
    fn send(&self, value: T) {
        self.queue.lock().unwrap().push_back(value);
    }
}

impl<T: Traverseable> Traverseable for Receiver<T> {
    fn traverse(&self, gc: &mut Gc) {
        self.queue.lock().unwrap().traverse(gc);
    }
}

pub struct Receiver<T> {
    queue: Arc<Mutex<VecDeque<T>>>,
}

impl<T> Userdata for Receiver<T>
where
    T: Any + Send + Sync + fmt::Debug + Traverseable,
{
}

impl<T> fmt::Debug for Receiver<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.queue.lock().unwrap())
    }
}

impl<T> Receiver<T> {
    fn try_recv(&self) -> Result<T, ()> {
        self.queue.lock().unwrap().pop_front().ok_or(())
    }
}

impl<T: VmType> VmType for Sender<T>
where
    T::Type: Sized,
{
    type Type = Sender<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let symbol = vm.global_env()
            .get_env()
            .find_type_info("Sender")
            .unwrap()
            .name
            .clone();
        Type::app(Type::ident(symbol), collect![T::make_type(vm)])
    }
}

impl<T: VmType> VmType for Receiver<T>
where
    T::Type: Sized,
{
    type Type = Receiver<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let symbol = vm.global_env()
            .get_env()
            .find_type_info("Receiver")
            .unwrap()
            .name
            .clone();
        Type::app(Type::ident(symbol), collect![T::make_type(vm)])
    }
}

field_decl!{ sender, receiver }

pub type ChannelRecord<S, R> = record_type!(sender => S, receiver => R);

/// FIXME The dummy `a` argument should not be needed to ensure that the channel can only be used
/// with a single type
fn channel(
    WithVM { vm, .. }: WithVM<Generic<A>>,
) -> ChannelRecord<Sender<Generic<A>>, Receiver<Generic<A>>> {
    let sender = Sender {
        thread: unsafe { GcPtr::from_raw(vm) },
        queue: Arc::new(Mutex::new(VecDeque::new())),
    };
    let receiver = Receiver {
        queue: sender.queue.clone(),
    };
    record_no_decl!(sender => sender, receiver => receiver)
}

fn recv(receiver: &Receiver<Generic<A>>) -> Result<Generic<A>, ()> {
    receiver.try_recv().map_err(|_| ())
}

fn send(sender: &Sender<Generic<A>>, value: Generic<A>) -> Result<(), ()> {
    unsafe {
        let value = sender
            .thread
            .deep_clone_value(&sender.thread, value.get_value())
            .map_err(|_| ())?;
        Ok(sender.send(Generic::from(value)))
    }
}

extern "C" fn resume(vm: &Thread) -> Status {
    let mut context = vm.context();
    let value = StackFrame::current(&mut context.stack)[0].get_repr();
    match value {
        ValueRepr::Thread(child) => {
            let lock = StackFrame::current(&mut context.stack).into_lock();
            drop(context);
            let result = child.resume();
            context = vm.context();
            context.stack.release_lock(lock);
            match result {
                Ok(child_context) => {
                    // Prevent dead lock if the following status_push call allocates
                    drop(child_context);

                    let value: Result<(), &str> = Ok(());
                    value.status_push(vm, &mut context)
                }
                Err(Error::Dead) => {
                    let value: Result<(), &str> = Err("Attempted to resume a dead thread");
                    value.status_push(vm, &mut context)
                }
                Err(err) => {
                    let fmt = format!("{}", err);
                    let result = unsafe {
                        ValueRepr::String(GcStr::from_utf8_unchecked(
                            context.alloc_ignore_limit(fmt.as_bytes()),
                        ))
                    };
                    context.stack.push(result);
                    Status::Error
                }
            }
        }
        _ => unreachable!(),
    }
}

extern "C" fn yield_(_vm: &Thread) -> Status {
    Status::Yield
}

fn spawn<'vm>(
    value: WithVM<'vm, Function<&'vm Thread, fn(())>>,
) -> RuntimeResult<RootedThread, Error> {
    spawn_(value).into()
}
fn spawn_<'vm>(value: WithVM<'vm, Function<&'vm Thread, fn(())>>) -> VmResult<RootedThread> {
    let thread = value.vm.new_thread()?;
    {
        let mut context = thread.context();
        let callable = match value.value.get_variant().0 {
            ValueRepr::Closure(c) => State::Closure(c),
            ValueRepr::Function(c) => State::Extern(c),
            _ => State::Unknown,
        };
        value.value.push(value.vm, &mut context)?;
        context.stack.push(ValueRepr::Int(0));
        StackFrame::current(&mut context.stack).enter_scope(1, callable);
    }
    Ok(thread)
}

type Action = fn(()) -> OpaqueValue<RootedThread, IO<Generic<A>>>;

#[cfg(target_arch = "wasm32")]
fn spawn_on<'vm>(
    _thread: RootedThread,
    _action: WithVM<'vm, FunctionRef<Action>>,
) -> IO<OpaqueValue<&'vm Thread, IO<Generic<A>>>> {
    IO::Exception("spawn_on requires the `tokio_core` crate".to_string())
}

#[cfg(not(target_arch = "wasm32"))]
fn spawn_on<'vm>(
    thread: RootedThread,
    action: WithVM<'vm, FunctionRef<Action>>,
) -> IO<OpaqueValue<&'vm Thread, IO<Generic<A>>>> {
    struct SpawnFuture<F>(Mutex<Option<F>>);

    impl<F> fmt::Debug for SpawnFuture<F> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "Future")
        }
    }

    impl<F> Userdata for SpawnFuture<F>
    where
        F: Send + 'static,
    {
    }

    impl<F> Traverseable for SpawnFuture<F> {
        fn traverse(&self, _: &mut Gc) {}
    }

    impl<F> VmType for SpawnFuture<F> {
        type Type = Generic<A>;
    }

    fn push_future_wrapper<G>(vm: &Thread, context: &mut OwnedContext, _: &G)
    where
        G: Future<Item = OpaqueValue<RootedThread, IO<Generic<A>>>, Error = Error> + Send + 'static,
    {
        extern "C" fn future_wrapper<F>(vm: &Thread) -> Status
        where
            F: Future<Item = OpaqueValue<RootedThread, IO<Generic<A>>>, Error = Error>
                + Send
                + 'static,
        {
            let mut context = vm.context();
            let value = StackFrame::current(&mut context.stack)[0].get_repr();

            match value {
                ValueRepr::Userdata(data) => {
                    let data = data.downcast_ref::<SpawnFuture<F>>().unwrap();
                    let future = data.0.lock().unwrap().take().unwrap();
                    let lock = StackFrame::current(&mut context.stack).insert_lock();
                    AsyncPushable::async_status_push(
                        FutureResult::new(future),
                        vm,
                        &mut context,
                        lock,
                    )
                }
                _ => unreachable!(),
            }
        }

        type FutureArg = ();
        primitive::<fn(FutureArg) -> IO<Generic<A>>>("unknown", future_wrapper::<G>)
            .push(vm, context)
            .unwrap();
    }
    use value::PartialApplicationDataDef;

    let WithVM { vm, value: action } = action;
    let mut action = OwnedFunction::<Action>::from_value(&thread, action.get_variant());

    let future = oneshot::spawn_fn(
        move || action.call_async(()),
        &vm.global_env().get_event_loop().expect("event loop"),
    );

    let mut context = vm.context();

    push_future_wrapper(vm, &mut context, &future);

    let callable = match context.stack[context.stack.len() - 1].get_repr() {
        ValueRepr::Function(ext) => Callable::Extern(ext),
        _ => unreachable!(),
    };

    SpawnFuture(Mutex::new(Some(future)))
        .push(vm, &mut context)
        .unwrap();
    let fields = [context.stack.get_values().last().unwrap().clone()];
    let def = PartialApplicationDataDef(callable, &fields);
    let value = ValueRepr::PartialApplication(context.alloc_with(vm, def).unwrap()).into();

    context.stack.pop_many(2);

    // TODO Remove rooting here
    IO::Value(OpaqueValue::from_value(vm.root_value(value)))
}

fn new_thread(WithVM { vm, .. }: WithVM<()>) -> IO<RootedThread> {
    match vm.new_thread() {
        Ok(thread) => IO::Value(thread),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn sleep(ms: VmInt) -> IO<()> {
    use std::time::Duration;
    ::std::thread::sleep(Duration::from_millis(ms as u64));
    IO::Value(())
}

fn interrupt(thread: RootedThread) -> IO<()> {
    thread.interrupt();
    IO::Value(())
}

mod std {
    pub use channel;
    pub mod thread {
        pub use channel as prim;
    }
}

pub fn load_channel<'vm>(vm: &'vm Thread) -> VmResult<ExternModule> {
    let _ = vm.register_type::<Sender<A>>("Sender", &["a"]);
    let _ = vm.register_type::<Receiver<A>>("Receiver", &["a"]);

    ExternModule::new(
        vm,
        record!{
            channel => primitive!(1 std::channel::channel),
            recv => primitive!(1 std::channel::recv),
            send => primitive!(2 std::channel::send),
        },
    )
}

pub fn load_thread<'vm>(vm: &'vm Thread) -> VmResult<ExternModule> {
    ExternModule::new(
        vm,
        record!{
            resume => primitive::<fn(&'vm Thread) -> Result<(), String>>("std.thread.prim.resume", resume),
            (yield_ "yield") => primitive::<fn(())>("std.thread.prim.yield", yield_),
            spawn => primitive!(1 std::thread::prim::spawn),
            spawn_on => primitive!(2 std::thread::prim::spawn_on),
            new_thread => primitive!(1 std::thread::prim::new_thread),
            interrupt => primitive!(1 std::thread::prim::interrupt),
            sleep => primitive!(1 std::thread::prim::sleep)
        },
    )
}
