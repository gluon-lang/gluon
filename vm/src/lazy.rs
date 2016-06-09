use std::marker::PhantomData;
use std::sync::Mutex;

use base::types;
use base::types::{Type, TcType};
use gc::{Gc, Traverseable};
use api::{Userdata, VMType, Pushable};
use api::generic::A;
use vm::{Status, Value, Thread, Result};


pub struct Lazy<T> {
    value: Mutex<Lazy_>,
    _marker: PhantomData<T>,
}

#[derive(Clone, Copy, PartialEq)]
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

impl<T> VMType for Lazy<T>
    where T: VMType,
          T::Type: Sized
{
    type Type = Lazy<T::Type>;

    fn make_type(vm: &Thread) -> TcType {
        let env = vm.get_env();
        let symbol = env.find_type_info("Lazy").unwrap().name.clone();
        let ctor = Type::id(symbol);
        types::Type::data(ctor, vec![T::make_type(vm)])
    }
}

fn force(vm: &Thread) -> Status {
    let mut stack = vm.current_frame();
    match stack[0] {
        Value::Userdata(lazy) => {
            let lazy = lazy.downcast_ref::<Lazy<A>>().expect("Lazy");
            let value = *lazy.value.lock().unwrap();
            match value {
                Lazy_::Blackhole => {
                    "<<loop>>".push(vm, &mut stack.stack);
                    Status::Error
                }
                Lazy_::Thunk(value) => {
                    stack.push(value);
                    stack.push(Value::Int(0));
                    *lazy.value.lock().unwrap() = Lazy_::Blackhole;
                    let result = vm.call_function(stack, 1);
                    match result {
                        Ok(None) => panic!("Expected stack"),
                        Ok(Some(mut stack)) => {
                            let value = stack.pop();
                            while stack.len() > 1 {
                                stack.pop();
                            }
                            *lazy.value.lock().unwrap() = Lazy_::Value(value);
                            stack.push(value);
                            Status::Ok
                        }
                        Err(err) => {
                            let mut stack = vm.get_stack();
                            let err = format!("{}", err);
                            err.push(vm, &mut stack);
                            Status::Error
                        }
                    }
                }
                Lazy_::Value(value) => {
                    stack[0] = value;
                    Status::Ok
                }
            }
        }
        x => panic!("Expected lazy got {:?}", x),
    }
}

fn lazy(vm: &Thread) -> Status {
    let mut stack = vm.current_frame();
    let f = stack[0];
    let lazy = Userdata(Lazy::<A> {
        value: Mutex::new(Lazy_::Thunk(f)),
        _marker: PhantomData,
    });
    lazy.push(vm, &mut stack.stack)
}

pub fn load(vm: &Thread) -> Result<()> {
    use api::primitive;
    try!(vm.define_global("lazy",
                          primitive::<fn(fn(()) -> A) -> Lazy<A>>("lazy", ::lazy::lazy)));
    try!(vm.define_global("force",
                          primitive::<fn(Lazy<A>) -> A>("force", ::lazy::force)));
    Ok(())
}
