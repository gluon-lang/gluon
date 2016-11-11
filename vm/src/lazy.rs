use std::any::Any;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Mutex;

use base::types;
use base::types::{Type, ArcType};
use base::fnv::FnvMap;
use gc::{Gc, GcPtr, Move, Traverseable};
use api::{OpaqueValue, Userdata, VmType};
use api::Generic;
use api::generic::A;
use vm::{Status, Thread};
use {Error, Result};
use value::{Value, deep_clone};
use stack::StackFrame;
use thread::ThreadInternal;

pub struct Lazy<T> {
    value: Mutex<Lazy_>,
    _marker: PhantomData<T>,
}

impl<T> Userdata for Lazy<T>
    where T: Any + Send + Sync,
{
    fn deep_clone(&self,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc,
                  thread: &Thread)
                  -> Result<GcPtr<Box<Userdata>>> {
        let value = self.value.lock().unwrap();
        let cloned_value = match *value {
            Lazy_::Blackhole => return Err(Error::Message("<<loop>>".into())),
            Lazy_::Thunk(value) => Lazy_::Thunk(try!(deep_clone(value, visited, gc, thread))),
            Lazy_::Value(value) => Lazy_::Value(try!(deep_clone(value, visited, gc, thread))),
        };
        let data: Box<Userdata> = Box::new(Lazy {
            value: Mutex::new(cloned_value),
            _marker: PhantomData::<A>,
        });
        gc.alloc(Move(data))
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
    where T: VmType,
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

extern "C" fn force(vm: &Thread) -> Status {
    let mut context = vm.context();
    let value = StackFrame::current(&mut context.stack)[0];
    match value {
        Value::Userdata(lazy) => {
            let lazy = lazy.downcast_ref::<Lazy<A>>().expect("Lazy");
            let value = *lazy.value.lock().unwrap();
            match value {
                Lazy_::Blackhole => {
                    let result = Value::String(context.alloc_ignore_limit("<<loop>>"));
                    context.stack.push(result);
                    Status::Error
                }
                Lazy_::Thunk(value) => {
                    context.stack.push(value);
                    context.stack.push(Value::Int(0));
                    *lazy.value.lock().unwrap() = Lazy_::Blackhole;
                    let result = vm.call_function(context, 1);
                    match result {
                        Ok(None) => panic!("Expected stack"),
                        Ok(Some(mut context)) => {
                            let mut stack = StackFrame::current(&mut context.stack);
                            let value = stack.pop();
                            while stack.len() > 1 {
                                stack.pop();
                            }
                            *lazy.value.lock().unwrap() = Lazy_::Value(value);
                            stack.push(value);
                            Status::Ok
                        }
                        Err(err) => {
                            let mut context = vm.context();
                            let err = format!("{}", err);
                            let result = Value::String(context.alloc_ignore_limit(&err[..]));
                            context.stack.push(result);
                            Status::Error
                        }
                    }
                }
                Lazy_::Value(value) => {
                    StackFrame::current(&mut context.stack)[0] = value;
                    Status::Ok
                }
            }
        }
        x => panic!("Expected lazy got {:?}", x),
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
    use api::primitive;
    try!(vm.define_global("lazy", primitive!(1 lazy)));
    try!(vm.define_global("force",
                          primitive::<fn(&'vm Lazy<A>) -> Generic<A>>("force", ::lazy::force)));
    Ok(())
}
