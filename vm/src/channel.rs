use std::any::Any;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

use base::types::{ArcType, Type};

use {Error, Result as VmResult};
use api::record::{Record, HList};
use api::{Generic, VmType, primitive, WithVM, Function, Pushable, RuntimeResult};
use api::generic::A;
use gc::{Traverseable, Gc, GcPtr};
use vm::{Thread, RootedThread, Status};
use thread::ThreadInternal;
use value::{Userdata, Value};
use stack::{State, StackFrame};

pub struct Sender<T> {
    // No need to traverse this thread reference as any thread having a reference to this `Sender`
    // would also directly own a reference to the `Thread`
    thread: GcPtr<Thread>,
    queue: Arc<Mutex<VecDeque<T>>>,
}

impl<T> Userdata for Sender<T> where T: Any + Send + Sync + fmt::Debug + Traverseable, {}

impl<T> fmt::Debug for Sender<T>
    where T: fmt::Debug,
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

impl<T> Userdata for Receiver<T> where T: Any + Send + Sync + fmt::Debug + Traverseable, {}

impl<T> fmt::Debug for Receiver<T>
    where T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self.queue.lock().unwrap())
    }
}

impl<T> Receiver<T> {
    fn try_recv(&self) -> Result<T, ()> {
        self.queue
            .lock()
            .unwrap()
            .pop_front()
            .ok_or(())
    }
}

impl<T: VmType> VmType for Sender<T>
    where T::Type: Sized,
{
    type Type = Sender<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let symbol = vm.global_env().get_env().find_type_info("Sender").unwrap().name.clone();
        Type::app(Type::ident(symbol), vec![T::make_type(vm)])
    }
}

impl<T: VmType> VmType for Receiver<T>
    where T::Type: Sized,
{
    type Type = Receiver<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let symbol = vm.global_env().get_env().find_type_info("Receiver").unwrap().name.clone();
        Type::app(Type::ident(symbol), vec![T::make_type(vm)])
    }
}

field_decl!{ sender, receiver }


pub type ChannelRecord<S, R> = Record<HList<(_field::sender, S), HList<(_field::receiver, R), ()>>>;

/// FIXME The dummy `a` argument should not be needed to ensure that the channel can only be used
/// with a single type
fn channel(WithVM { vm, .. }: WithVM<Generic<A>>)
           -> ChannelRecord<Sender<Generic<A>>, Receiver<Generic<A>>> {
    let sender = Sender {
        thread: unsafe { GcPtr::from_raw(vm) },
        queue: Arc::new(Mutex::new(VecDeque::new())),
    };
    let receiver = Receiver { queue: sender.queue.clone() };
    record_no_decl!(sender => sender, receiver => receiver)
}

fn recv(receiver: &Receiver<Generic<A>>) -> Result<Generic<A>, ()> {
    receiver.try_recv()
        .map_err(|_| ())
}

fn send(sender: &Sender<Generic<A>>, value: Generic<A>) -> Result<(), ()> {
    let value = try!(sender.thread.deep_clone(value.0).map_err(|_| ()));
    Ok(sender.send(Generic::from(value)))
}

fn resume(vm: &Thread) -> Status {
    let mut context = vm.context();
    let value = StackFrame::current(&mut context.stack)[0];
    match value {
        Value::Thread(child) => {
            let lock = StackFrame::current(&mut context.stack).into_lock();
            drop(context);
            let result = child.resume();
            context = vm.context();
            context.stack.release_lock(lock);
            match result {
                Ok(()) |
                Err(Error::Yield) => {
                    let value: Result<(), &str> = Ok(());
                    value.status_push(vm, &mut context)
                }
                Err(Error::Dead) => {
                    let value: Result<(), &str> = Err("Attempted to resume a dead thread");
                    value.status_push(vm, &mut context)
                }
                Err(err) => {
                    let fmt = format!("{}", err);
                    let result = Value::String(context.alloc_ignore_limit(&fmt[..]));
                    context.stack.push(result);
                    Status::Error
                }
            }
        }
        _ => unreachable!(),
    }
}

fn yield_(_vm: &Thread) -> Status {
    Status::Yield
}

fn spawn<'vm>(value: WithVM<'vm, Function<&'vm Thread, fn(())>>)
              -> RuntimeResult<RootedThread, Error> {
    match spawn_(value) {
        Ok(x) => RuntimeResult::Return(x),
        Err(err) => RuntimeResult::Panic(err),
    }
}
fn spawn_<'vm>(value: WithVM<'vm, Function<&'vm Thread, fn(())>>) -> VmResult<RootedThread> {
    let thread = try!(value.vm.new_thread());
    {
        let mut context = thread.context();
        let callable = match value.value.value() {
            Value::Closure(c) => State::Closure(c),
            Value::Function(c) => State::Extern(c),
            _ => State::Unknown,
        };
        try!(value.value.push(value.vm, &mut context));
        context.stack.push(Value::Int(0));
        StackFrame::current(&mut context.stack).enter_scope(1, callable);
    }
    Ok(thread)
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}

pub fn load(vm: &Thread) -> VmResult<()> {
    let _ = vm.register_type::<Sender<A>>("Sender", &["a"]);
    let _ = vm.register_type::<Receiver<A>>("Receiver", &["a"]);
    try!(vm.define_global("channel", f1(channel)));
    try!(vm.define_global("recv", f1(recv)));
    try!(vm.define_global("send", f2(send)));
    try!(vm.define_global("resume",
                          primitive::<fn(RootedThread) -> Result<(), String>>("resume", resume)));
    try!(vm.define_global("yield", primitive::<fn(())>("yield", yield_)));
    try!(vm.define_global("spawn", f1(spawn)));
    Ok(())
}
