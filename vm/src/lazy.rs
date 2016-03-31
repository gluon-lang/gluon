use base::types;
use base::types::TcType;
use std::marker::PhantomData;
use gc::{Gc, Traverseable, Move};
use std::cell::Cell;
use api::{VMType, Pushable};
use vm::{Status, Value, VM, Result};


#[derive(Clone, PartialEq)]
pub struct Lazy<T> {
    value: Cell<Lazy_>,
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
        match self.value.get() {
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

    fn make_type(vm: &VM) -> TcType {
        use base::symbol::Symbol;
        use base::types::TypeEnv;
        let env = vm.env();
        // FIXME Inefficient
        let symbol = env.find_type_info(&Symbol::new("Lazy")).unwrap().name.clone();
        let ctor = types::TypeConstructor::Data(symbol);
        types::Type::data(ctor, vec![T::make_type(vm)])
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
    let lazy = vm.alloc(&stack.stack,
                        Move(Lazy {
                            value: Cell::new(Lazy_::Thunk(f)),
                            _marker: PhantomData,
                        }));
    stack.push(Value::Lazy(lazy));
    Status::Ok
}

pub fn load(vm: &VM) -> Result<()> {
    use api::generic::A;
    use api::primitive;
    try!(vm.define_global("lazy",
                          primitive::<fn(fn(()) -> A) -> Lazy<A>>("lazy", ::lazy::lazy)));
    try!(vm.define_global("force",
                          primitive::<fn(Lazy<A>) -> A>("force", ::lazy::force)));
    Ok(())
}
