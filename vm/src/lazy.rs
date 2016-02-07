use base::types;
use base::types::TcType;
use std::marker::PhantomData;
use gc::{Gc, Traverseable, Move};
use std::cell::Cell;
use api::{VMType, Pushable};
use vm::{Status, Value, VM, VMResult};


#[derive(Clone, PartialEq)]
pub struct Lazy<'a, T> {
    value: Cell<Lazy_<'a>>,
    _marker: PhantomData<T>,
}

#[derive(Clone, Copy, PartialEq)]
enum Lazy_<'a> {
    Blackhole,
    Thunk(Value<'a>),
    Value(Value<'a>),
}

impl<'a, T> Traverseable for Lazy<'a, T> {
    fn traverse(&self, gc: &mut Gc) {
        match self.value.get() {
            Lazy_::Blackhole => (),
            Lazy_::Thunk(value) => value.traverse(gc),
            Lazy_::Value(value) => value.traverse(gc),
        }
    }
}

impl<'a, T> VMType for Lazy<'a, T>
    where T: VMType,
          T::Type: Sized
{
    type Type = Lazy<'static, T::Type>;

    fn make_type(vm: &VM) -> TcType {
        types::Type::data(types::TypeConstructor::Data(vm.symbol("Lazy")),
                          vec![T::make_type(vm)])
    }
}

fn force(vm: &VM) -> Status {
    let mut stack = vm.current_frame();
    match stack[0] {
        Value::Lazy(lazy) => {
            match lazy.value.get() {
                Lazy_::Blackhole => {
                    "<<loop>>".push(vm, &mut stack);
                    Status::Error
                }
                Lazy_::Thunk(value) => {
                    stack.push(value);
                    stack.push(Value::Int(0));
                    lazy.value.set(Lazy_::Blackhole);
                    let result = vm.call_function(stack, 1);
                    match result {
                        Ok(None) => panic!("Expected stack"),
                        Ok(Some(mut stack)) => {
                            let value = stack.pop();
                            while stack.len() > 1 {
                                stack.pop();
                            }
                            lazy.value.set(Lazy_::Value(value));
                            stack.push(value);
                            Status::Ok
                        }
                        Err(err) => {
                            let mut stack = vm.current_frame();
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

fn lazy(vm: &VM) -> Status {
    let mut stack = vm.current_frame();
    let f = stack[0];
    let lazy = vm.alloc(&stack.stack, Move(Lazy {
        value: Cell::new(Lazy_::Thunk(f)),
        _marker: PhantomData,
    }));
    stack.push(Value::Lazy(lazy));
    Status::Ok
}

pub fn load(vm: &VM) -> VMResult<()> {
    use api::generic::A;
    use api::primitive;
    try!(vm.define_global("lazy",
                          primitive::<fn(fn(()) -> A) -> Lazy<'static, A>>("lazy", ::lazy::lazy)));
    try!(vm.define_global("force",
                          primitive::<fn(Lazy<'static, A>) -> A>("force", ::lazy::force)));
    Ok(())
}
