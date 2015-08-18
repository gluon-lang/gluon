
use base::interner::InternedStr;
use base::ast::Type;
use api::{Callable, Getable, Pushable, Generic, VMType};
use api::generic::A;
use types::VMIndex;
use vm::{Root, StackFrame, Status, Value, VM, Userdata_};


#[derive(Clone, Copy)]
pub enum Lazy<T> {
    Thunk(T),
    Value(T)
}

impl <'a> VMType for Lazy<Generic<'a, A>> {
    fn vm_type<'b>(vm: &'b VM) -> &'b Type<InternedStr> {
        vm.get_type::<Lazy<Generic<'static, A>>>()
    }
}

impl <'a> Pushable<'a> for Lazy<Generic<'a, A>> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let self_= unsafe {
            ::std::mem::transmute::<Lazy<Generic<'a, A>>, Lazy<Generic<'static, A>>>(self)
        };
        stack.push(Value::Userdata(Userdata_::new(vm, self_)));
        Status::Ok
    }
}

pub fn force<'vm, 'a>(value: Root<'vm, Lazy<Generic<'a, A>>>) -> Generic<'a, A> {
    panic!()
}

pub fn lazy<'vm, 'a>(value: Root<'vm, Callable<'vm, 'a, ((),), Generic<'a, A>>>) {
    panic!()
}
