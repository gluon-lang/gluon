use base::gc::{Gc, Traverseable, Move};
use std::cell::Cell;
use api::Pushable;
use vm::{StackFrame, Status, Value, VM};


#[derive(Clone, PartialEq)]
pub struct Lazy<'a> {
    value: Cell<Lazy_<'a>>
}

#[derive(Clone, Copy, PartialEq)]
enum Lazy_<'a> {
    Blackhole,
    Thunk(Value<'a>),
    Value(Value<'a>)
}

impl <'a> Traverseable for Lazy<'a> {
    fn traverse(&self, gc: &mut Gc) {
        match self.value.get() {
            Lazy_::Blackhole => (),
            Lazy_::Thunk(value) => value.traverse(gc),
            Lazy_::Value(value) => value.traverse(gc),
        }
    }
}

pub fn force(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    println!("{:?}", stack.stack.values);
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
                    let frame = stack.frame;
                    drop(stack);
                    let result = vm.execute_call(1);
                    stack = StackFrame { stack: vm.stack.borrow_mut(), frame: frame };
                    match result {
                        Ok(value) => {
                            while stack.len() > 1 {
                                stack.pop();
                            }
                            lazy.value.set(Lazy_::Value(value));
                            stack.push(value);
                            Status::Ok
                        }
                        Err(err) => {
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
        x => panic!("Expected lazy got {:?}", x)
    }
}

pub fn lazy(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    let f = stack[0];
    let lazy = vm.gc.borrow_mut().alloc(Move(Lazy { value: Cell::new(Lazy_::Thunk(f)) }));
    stack.push(Value::Lazy(lazy));
    Status::Ok
}
