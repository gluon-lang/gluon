//! This example uses [hyper][] to create a http server which handles requests asynchronously in
//! gluon. To do this we define a few types and functions in Rust with which we register in gluon
//! so that we can communicate with `hyper`. The rest of the implementation is done in gluon,
//! routing the requests and constructing the responses.
//!
//! [hyper]:https://hyper.rs

extern crate gluon;
extern crate gluon_base as base;
#[macro_use]
extern crate gluon_vm as vm;

#[macro_use]
extern crate collect_mac;
extern crate env_logger;
extern crate futures;
extern crate hyper;
#[macro_use]
extern crate log;

use std::env;
use std::fmt;
use std::error::Error as StdError;
use std::fs::File;
use std::io::{stderr, Read, Write};
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

use hyper::{Chunk, Method, StatusCode};
use hyper::server::Service;

use futures::Async;
use futures::future::Future;
use futures::sink::Sink;
use futures::stream::Stream;
use futures::sync::mpsc::Sender;

use base::types::{ArcType, Type};

use vm::{Error as VmError, ExternModule, Result as VmResult};

use vm::thread::ThreadInternal;
use vm::thread::{Context, RootedThread, Thread};
use vm::Variants;
use vm::api::{Function, FunctionRef, FutureResult, Getable, OpaqueValue, PushAsRef, Pushable,
              Userdata, ValueRef, VmType, WithVM, IO};
use vm::gc::{Gc, Traverseable};
use gluon::import::add_extern_module;

use vm::internal::Value;

use gluon::{new_vm, Compiler};

// `Handler` is a type defined in http.glu but since we need to refer to it in the signature of
// listen we define a phantom type which we can use with `OpaqueValue` to store a `Handler` in Rust
struct Handler<T>(PhantomData<T>);

impl<T: VmType + 'static> VmType for Handler<T> {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        let typ = (*vm.global_env()
            .get_env()
            .find_type_info("examples.http_types.Handler")
            .unwrap())
            .clone()
            .into_type();
        Type::app(typ, collect![T::make_type(vm)])
    }
}

// Rust does not let us define traits on types defined in a different crate such as `hyper`. We can
// however work around this by defining a wrapper type which we are then able to define the traits
// on.
struct Wrap<T>(T);

macro_rules! define_vmtype {
    ($name: ident) => {
        impl VmType for Wrap<$name> {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                let typ = concat!("examples.http_types.", stringify!($name));
                (*vm.global_env().get_env().find_type_info(typ).unwrap())
                    .clone()
                    .into_type()
            }
        }

    }
}

define_vmtype! { Method }

impl<'vm> Pushable<'vm> for Wrap<Method> {
    fn push(self, _: &'vm Thread, context: &mut Context) -> VmResult<()> {
        use hyper::Method::*;
        context.stack.push(Value::tag(match self.0 {
            Get => 0,
            Post => 1,
            Delete => 2,
            _ => {
                return Err(VmError::Message(format!(
                    "Method `{:?}` does not exist in gluon",
                    self.0
                )).into())
            }
        }));
        Ok(())
    }
}

define_vmtype! { StatusCode }

impl<'vm> Getable<'vm> for Wrap<StatusCode> {
    fn from_value(_: &'vm Thread, value: Variants) -> Self {
        use hyper::StatusCode::*;
        match value.as_ref() {
            ValueRef::Data(data) => Wrap(match data.tag() {
                0 => Ok,
                1 => NotFound,
                2 => InternalServerError,
                _ => panic!("Unexpected tag"),
            }),
            _ => panic!(),
        }
    }
}

// Representation of a http body that is in the prograss of being read
pub struct Body(Arc<Mutex<Box<Stream<Item = PushAsRef<Chunk, [u8]>, Error = VmError> + Send>>>);

// By implementing `Userdata` on `Body` it can be automatically pushed and retrieved from gluon
// threads
impl Userdata for Body {}

// Types implementing `Userdata` requires a `std::fmt::Debug` implementation so it can be displayed
impl fmt::Debug for Body {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "hyper::Body")
    }
}

// `Traverseable` is required by `Userdata` so that the garbage collector knows how to scan the
// value for garbage collected references. Normally objects do not contain any references so this
// can be empty
impl Traverseable for Body {
    fn traverse(&self, _: &mut Gc) {}
}

// `VmType` is the last trait required for a type to implement `Userdata` and defines the type used
// in gluon for this Rust type. For opaque `Userdata` values this minimal implementation is enough
// as the default implementation of `make_type` will lookup `VmType::Type` from the virtual machine
// which should have been registered earlier with `Thread::register_type`
impl VmType for Body {
    type Type = Self;
}

// Since `Body` implements `Userdata` gluon will automatically marshal the gluon representation
// into `&Body` argument
fn read_chunk(
    body: &Body,
) -> FutureResult<
    Box<Future<Item = IO<Option<PushAsRef<Chunk, [u8]>>>, Error = VmError> + Send + 'static>,
> {
    use futures::future::poll_fn;

    let body = body.0.clone();
    // `FutureResult` is a wrapper type around `Future` which when returned to the interpreter is
    // polled until completion. After `poll` returns `Ready` the value is then returned to the
    // gluon function which called `read_chunk`
    FutureResult(Box::new(poll_fn(move || {
        let mut stream = body.lock().unwrap();
        stream.poll().map(|async| async.map(IO::Value))
    })))
}

// A http body that is being written
pub struct ResponseBody(Arc<Mutex<Option<Sender<Result<Chunk, hyper::Error>>>>>);

impl fmt::Debug for ResponseBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "hyper::Response")
    }
}

impl Userdata for ResponseBody {}

impl Traverseable for ResponseBody {
    fn traverse(&self, _: &mut Gc) {}
}

impl VmType for ResponseBody {
    type Type = Self;
}

fn write_response(
    response: &ResponseBody,
    bytes: &[u8],
) -> FutureResult<Box<Future<Item = IO<()>, Error = VmError> + Send + 'static>> {
    use futures::future::poll_fn;
    use futures::AsyncSink;

    // Turn `bytes´ into a `Chunk` which can be sent to the http body
    let mut unsent_chunk = Some(Ok(bytes.to_owned().into()));
    let response = response.0.clone();
    FutureResult(Box::new(poll_fn(move || {
        info!("Starting response send");
        let mut sender = response.lock().unwrap();
        let sender = sender
            .as_mut()
            .expect("Sender has been dropped while still in use");
        if let Some(chunk) = unsent_chunk.take() {
            match sender.start_send(chunk) {
                Ok(AsyncSink::NotReady(chunk)) => {
                    unsent_chunk = Some(chunk);
                    return Ok(Async::NotReady);
                }
                Ok(AsyncSink::Ready) => (),
                Err(_) => {
                    info!("Could not send http response");
                    return Ok(Async::Ready(IO::Value(())));
                }
            }
        }
        match sender.poll_complete() {
            Ok(async) => Ok(async.map(IO::Value)),
            Err(_) => {
                info!("Could not send http response");
                Ok(Async::Ready(IO::Value(())))
            }
        }
    })))
}

// Next we define some record types which are marshalled to and from gluon. These have equivalent
// definitions in http_types.glu
field_decl! { method, uri, status, body, request, response }

type Request = record_type!{
    method => Wrap<Method>,
    uri => String,
    body => Body
};

type Response = record_type!{
    status => Wrap<StatusCode>
};

type HttpState = record_type!{
    request => Request,
    response => ResponseBody
};

fn listen(port: i32, value: WithVM<OpaqueValue<RootedThread, Handler<Response>>>) -> IO<()> {
    let WithVM {
        value: handler,
        vm: thread,
    } = value;

    use hyper::server::{Http, Request as HyperRequest, Response as HyperResponse};

    // Retrieve the `handle` function from the http module which we use to evaluate values of type
    // `Handler Response`
    type ListenFn = fn(OpaqueValue<RootedThread, Handler<Response>>, HttpState) -> IO<Response>;
    let handle: Function<RootedThread, ListenFn> = thread
        .get_global("examples.http.handle")
        .unwrap_or_else(|err| panic!("{}", err));

    struct Listen {
        handle: Function<RootedThread, ListenFn>,
        handler: OpaqueValue<RootedThread, Handler<Response>>,
    }

    impl Service for Listen {
        type Request = HyperRequest;
        type Response = HyperResponse;
        type Error = hyper::Error;
        type Future = Box<Future<Item = HyperResponse, Error = hyper::Error> + Send + 'static>;

        fn call(&self, request: HyperRequest) -> Self::Future {
            let gluon_request = record_no_decl! {
                // Here we use to `Wrap` type to make `hyper::Request` into a type that can be
                // pushed to gluon
                method => Wrap(request.method().clone()),
                uri => request.uri().to_string(),
                // Since `Body` implements `Userdata` it can be directly pushed to gluon
                body => Body(Arc::new(Mutex::new(Box::new(request.body()
                    .map_err(|err| VmError::Message(format!("{}", err)))
                    // `PushAsRef` makes the `body` parameter act as a `&[u8]` which means it is
                    // marshalled to `Array Byte` in gluon
                    .map(PushAsRef::<_, [u8]>::new)))))
            };
            let (response_sender, response_body) = hyper::Body::pair();
            let response_sender = Arc::new(Mutex::new(Some(response_sender)));
            let http_state = record_no_decl!{
                request => gluon_request,
                response => ResponseBody(response_sender.clone())
            };

            Box::new(
                self.handle
                    .clone()
                    .call_async(self.handler.clone(), http_state)
                    .then(move |result| match result {
                        Ok(value) => {
                            match value {
                                IO::Value(record_p!{ status }) => {
                                    // Drop the sender to so that it the receiver stops waiting for
                                    // more chunks
                                    *response_sender.lock().unwrap() = None;
                                    Ok(
                                        HyperResponse::new()
                                            .with_status(status.0)
                                            .with_body(response_body),
                                    )
                                }
                                IO::Exception(err) => {
                                    let _ = stderr().write(err.as_bytes());
                                    Ok(
                                        HyperResponse::new()
                                            .with_status(StatusCode::InternalServerError),
                                    )
                                }
                            }
                        }
                        Err(err) => {
                            let _ = stderr().write(format!("{}", err).as_bytes());
                            Ok(HyperResponse::new().with_status(StatusCode::InternalServerError))
                        }
                    }),
            )
        }
    }

    let addr = format!("127.0.0.1:{}", port).parse().unwrap();
    let result = Http::new()
        .bind(&addr, move || {
            Ok(Listen {
                handle: handle.clone(),
                handler: handler.clone(),
            })
        })
        .and_then(|server| server.run());

    match result {
        Ok(()) => IO::Value(()),
        Err(err) => IO::Exception(format!("{}", err)),
    }
}

// To let the `http_types` module refer to `Body` and `ResponseBody` we register these types in a
// separate function which is called before loading `http_types`
pub fn load_types(vm: &Thread) -> VmResult<()> {
    vm.register_type::<Body>("Body", &[])?;
    vm.register_type::<ResponseBody>("ResponseBody", &[])?;
    Ok(())
}

pub fn load(vm: &Thread) -> VmResult<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            listen => primitive!(2 listen),
            read_chunk => primitive!(1 read_chunk),
            write_response => primitive!(2 write_response)
        },
    )
}

fn main() {
    if let Err(err) = main_() {
        panic!("{}", err)
    }
}

fn main_() -> Result<(), Box<StdError>> {
    let _ = env_logger::try_init();
    let port = env::args()
        .nth(1)
        .map(|port| port.parse::<i32>().expect("port"))
        .unwrap_or(80);

    let thread = new_vm();

    // First load all the http types so we can refer to them from gluon
    load_types(&thread)?;
    Compiler::new().run_expr::<()>(
        &thread,
        "",
        r#"let _ = import! "examples/http_types.glu" in () "#,
    )?;

    // Load the primitive functions we define in this module
    add_extern_module(&thread, "http.prim", load);

    // Last we run our `http_server.glu` module which returns a function which starts listening
    // on the port we passed from the command line
    let mut expr = String::new();
    {
        let mut file = File::open("examples/http_server.glu")?;
        file.read_to_string(&mut expr)?;
    }
    let (mut listen, _) =
        Compiler::new().run_expr::<FunctionRef<fn(i32) -> IO<()>>>(&thread, "http_test", &expr)?;

    listen.call(port)?;
    Ok(())
}
