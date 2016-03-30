use base::symbol::Symbol;
use base::types::{TcType, Type, TypeConstructor, TypeEnv};
use base::types;
use api::record::{Record, HList};
use api::{Generic, Userdata, VMType};
use api::generic::A;
use vm::{VM, Result as VMResult};

use std::sync::mpsc;

impl <T: VMType> VMType for mpsc::Sender<T> where T::Type: Sized {
    type Type = mpsc::Sender<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.env().find_type_info(&Symbol::new("Sender")).unwrap().name.clone();
        let ctor = TypeConstructor::Data(symbol);
        Type::data(ctor, vec![T::make_type(vm)])
    }
}

impl <T: VMType> VMType for mpsc::Receiver<T> where T::Type: Sized {
    type Type = mpsc::Receiver<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.env().find_type_info(&Symbol::new("Receiver")).unwrap().name.clone();
        let ctor = TypeConstructor::Data(symbol);
        Type::data(ctor, vec![T::make_type(vm)])
    }
}

field_decl!{ sender, receiver }

fn channel(_: ()) -> Record<HList<(_field::sender, Userdata<mpsc::Sender<Generic<A>>>),
                       HList<(_field::receiver, Userdata<mpsc::Receiver<Generic<A>>>), ()>>>
{
    let (sender, receiver) = mpsc::channel();
    record_no_decl!(sender => Userdata(sender), receiver => Userdata(receiver))
}

fn recv(receiver: *const mpsc::Receiver<Generic<A>>) -> Result<Generic<A>, ()> {
    unsafe {
        let receiver = &*receiver;
        receiver.recv()
            .map_err(|_| ())
    }
}

fn send(sender: *const mpsc::Sender<Generic<A>>, value: Generic<A>) -> Result<(), ()> {
    unsafe {
        let sender = &*sender;
        sender.send(value)
            .map_err(|_| ())
    }
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
    let _ = vm.register_type::<mpsc::Sender<A>>("Sender", args.clone());
    let _ = vm.register_type::<mpsc::Receiver<A>>("Receiver", args);
    try!(vm.define_global("channel", f1(channel)));
    try!(vm.define_global("recv", f1(recv)));
    try!(vm.define_global("send", f2(send)));
    Ok(())
}
