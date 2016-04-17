use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

use base::symbol::Symbol;
use base::types::{TcType, Type, TypeConstructor};
use base::types;
use api::record::{Record, HList};
use api::{Generic, Userdata, VMType, primitive, WithVM, Function, Pushable};
use api::generic::A;
use gc::{Traverseable, Gc};
use vm::{Error, Thread, Value, VM, Result as VMResult, Status};
use stack::State;

struct Sender<T> {
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


struct Receiver<T> {
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
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.get_env().find_type_info("Sender").unwrap().name.clone();
        let ctor = TypeConstructor::Data(symbol);
        Type::data(ctor, vec![T::make_type(vm)])
    }
}

impl<T: VMType> VMType for Receiver<T>
    where T::Type: Sized
{
    type Type = Receiver<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.get_env().find_type_info("Receiver").unwrap().name.clone();
        let ctor = TypeConstructor::Data(symbol);
        Type::data(ctor, vec![T::make_type(vm)])
    }
}

field_decl!{ sender, receiver }

fn channel(_: ())
           -> Record<HList<(_field::sender, Userdata<Sender<Generic<A>>>),
                           HList<(_field::receiver, Userdata<Receiver<Generic<A>>>), ()>>> {
    let sender = Sender { queue: Arc::new(Mutex::new(VecDeque::new())) };
    let receiver = Receiver { queue: sender.queue.clone() };
    record_no_decl!(sender => Userdata(sender), receiver => Userdata(receiver))
}

fn recv(receiver: *const Receiver<Generic<A>>) -> Result<Generic<A>, ()> {
    unsafe {
        let receiver = &*receiver;
        receiver.try_recv()
                .map_err(|_| ())
    }
}

fn send(sender: *const Sender<Generic<A>>, value: Generic<A>) -> Result<(), ()> {
    unsafe {
        let sender = &*sender;
        Ok(sender.send(value))
    }
}

fn resume(vm: &VM) -> Status {
    let mut stack = vm.current_frame();
    match stack[0] {
        Value::Thread(thread) => {
            drop(stack);
            let child = VM::from_gc_ptr(thread);
            let result = child.resume();
            stack = vm.current_frame();
            match result {
                Ok(()) |
                Err(Error::Yield) => {
                    let value: Result<(), &str> = Ok(());
                    value.push(vm, &mut stack);
                    Status::Ok
                }
                Err(Error::Dead) => {
                    let value: Result<(), &str> = Err("Attempted to resume a dead thread");
                    value.push(vm, &mut stack);
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

fn yield_(_vm: &VM) -> Status {
    Status::Yield
}

fn spawn<'vm>(value: WithVM<'vm, Function<'vm, fn(())>>) -> Thread {
    let thread = value.vm.new_thread();
    {
        let mut stack = thread.current_frame();
        let callable = match value.value.value() {
            Value::Closure(c) => State::Closure(c),
            Value::Function(c) => State::Extern(c),
            _ => State::Unknown,
        };
        value.value.push(value.vm, &mut stack);
        stack.push(Value::Int(0));
        stack.enter_scope(1, callable);
    }
    thread
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}

pub fn load(vm: &VM) -> VMResult<()> {
    let args = vec![types::Generic {
                        id: Symbol::new("a"),
                        kind: types::Kind::star(),
                    }];
    let _ = vm.register_type::<Sender<A>>("Sender", args.clone());
    let _ = vm.register_type::<Receiver<A>>("Receiver", args);
    try!(vm.define_global("channel", f1(channel)));
    try!(vm.define_global("recv", f1(recv)));
    try!(vm.define_global("send", f2(send)));
    try!(vm.define_global("resume",
                          primitive::<fn(Thread) -> Result<(), String>>("resume", resume)));
    try!(vm.define_global("yield", primitive::<fn(())>("yield", yield_)));
    try!(vm.define_global("spawn", f1(spawn)));
    Ok(())
}
