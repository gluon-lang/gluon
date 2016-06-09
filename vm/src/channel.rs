use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

use base::types::{TcType, Type};
use api::record::{Record, HList};
use api::{Generic, Userdata, VMType, primitive, WithVM, Function, Pushable};
use api::generic::A;
use gc::{Traverseable, Gc, GcPtr};
use vm::{Error, Thread, Value, RootedThread, Result as VMResult, Status};
use stack::{State, StackFrame};

pub struct Sender<T> {
    // No need to traverse this thread reference as any thread having a reference to this `Sender`
    // would also directly own a reference to the `Thread`
    thread: GcPtr<Thread>,
    queue: Arc<Mutex<VecDeque<T>>>,
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

impl<T> Receiver<T> {
    fn try_recv(&self) -> Result<T, ()> {
        self.queue
            .lock()
            .unwrap()
            .pop_front()
            .ok_or(())
    }
}

impl<T: VMType> VMType for Sender<T>
    where T::Type: Sized
{
    type Type = Sender<T::Type>;
    fn make_type(vm: &Thread) -> TcType {
        let symbol = vm.get_env().find_type_info("Sender").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![T::make_type(vm)])
    }
}

impl<T: VMType> VMType for Receiver<T>
    where T::Type: Sized
{
    type Type = Receiver<T::Type>;
    fn make_type(vm: &Thread) -> TcType {
        let symbol = vm.get_env().find_type_info("Receiver").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![T::make_type(vm)])
    }
}

field_decl!{ sender, receiver }


pub type ChannelRecord<S, R> = Record<HList<(_field::sender, S), HList<(_field::receiver, R), ()>>>;

/// FIXME The dummy `a` argument should not be needed to ensure that the channel can only be used
/// with a single type
fn channel(WithVM { vm, .. }: WithVM<Generic<A>>)
           -> ChannelRecord<Userdata<Sender<Generic<A>>>, Userdata<Receiver<Generic<A>>>> {
    let sender = Sender {
        thread: unsafe { GcPtr::from_raw(vm) },
        queue: Arc::new(Mutex::new(VecDeque::new())),
    };
    let receiver = Receiver { queue: sender.queue.clone() };
    record_no_decl!(sender => Userdata(sender), receiver => Userdata(receiver))
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
    let mut stack = vm.current_frame();
    match stack[0] {
        Value::Thread(thread) => {
            drop(stack);
            let child = RootedThread::from_gc_ptr(thread);
            let result = child.resume();
            stack = vm.current_frame();
            match result {
                Ok(()) |
                Err(Error::Yield) => {
                    let value: Result<(), &str> = Ok(());
                    value.push(vm, &mut stack.stack);
                    Status::Ok
                }
                Err(Error::Dead) => {
                    let value: Result<(), &str> = Err("Attempted to resume a dead thread");
                    value.push(vm, &mut stack.stack);
                    Status::Ok
                }
                Err(err) => {
                    let fmt = format!("{}", err);
                    let result = Value::String(vm.alloc(&stack.stack, &fmt[..]));
                    stack.push(result);
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

fn spawn<'vm>(value: WithVM<'vm, Function<&'vm Thread, fn(())>>) -> RootedThread {
    let thread = value.vm.new_thread();
    {
        let mut stack = thread.get_stack();
        let callable = match value.value.value() {
            Value::Closure(c) => State::Closure(c),
            Value::Function(c) => State::Extern(c),
            _ => State::Unknown,
        };
        value.value.push(value.vm, &mut stack);
        stack.push(Value::Int(0));
        StackFrame::current(stack).enter_scope(1, callable);
    }
    thread
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}

pub fn load(vm: &Thread) -> VMResult<()> {
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
