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
extern crate http;
extern crate hyper;
extern crate tokio;
#[macro_use]
extern crate log;

use std::env;
use std::error::Error as StdError;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

use hyper::service::Service;
use hyper::Chunk;
use hyper::Server;

use http::StatusCode;

use futures::future::Either;
use futures::stream::Stream;
use futures::sync::oneshot;
use futures::{future, Async, Future};

use base::types::{ArcType, Type};

use vm::{Error as VmError, ExternModule, Result as VmResult};

use gluon::import::add_extern_module;
use vm::api::{
    Function, FutureResult, OpaqueValue, OwnedFunction, PushAsRef, Userdata, VmType, WithVM, IO,
};
use vm::future::FutureValue;
use vm::gc::{Gc, Traverseable};
use vm::thread::{RootedThread, Thread};

use gluon::{new_vm, Compiler};

// `Handler` is a type defined in http.glu but since we need to refer to it in the signature of
// listen we define a phantom type which we can use with `OpaqueValue` to store a `Handler` in Rust
struct Handler<T>(PhantomData<T>);

impl<T: VmType + 'static> VmType for Handler<T> {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        let typ = vm
            .find_type_info("examples.http.types.Handler")
            .unwrap_or_else(|err| panic!("{}", err))
            .into_type();
        Type::app(typ, collect![T::make_type(vm)])
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
) -> FutureResult<impl Future<Item = IO<Option<PushAsRef<Chunk, [u8]>>>, Error = VmError>> {
    use futures::future::poll_fn;

    let body = body.0.clone();
    // `FutureResult` is a wrapper type around `Future` which when returned to the interpreter is
    // polled until completion. After `poll` returns `Ready` the value is then returned to the
    // gluon function which called `read_chunk`
    FutureResult(poll_fn(move || {
        let mut stream = body.lock().unwrap();
        stream.poll().map(|async| async.map(IO::Value))
    }))
}

// A http body that is being written
pub struct ResponseBody(Arc<Mutex<Option<hyper::body::Sender>>>);

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
) -> FutureResult<impl Future<Item = IO<()>, Error = VmError>> {
    use futures::future::poll_fn;

    // Turn `bytes´ into a `Chunk` which can be sent to the http body
    let mut unsent_chunk = Some(bytes.to_owned().into());
    let response = response.0.clone();
    FutureResult(poll_fn(move || {
        info!("Starting response send");
        let mut sender = response.lock().unwrap();
        let sender = sender
            .as_mut()
            .expect("Sender has been dropped while still in use");
        let chunk = unsent_chunk
            .take()
            .expect("Attempt to poll after chunk is sent");
        match sender.poll_ready() {
            Ok(Async::NotReady) => {
                unsent_chunk = Some(chunk);
                return Ok(Async::NotReady);
            }
            Ok(Async::Ready(_)) => (),
            Err(_) => {
                info!("Could not send http response");
                return Ok(Async::Ready(IO::Value(())));
            }
        }
        match sender.send_data(chunk) {
            Ok(()) => Ok(Async::Ready(IO::Value(()))),
            Err(chunk) => {
                info!("Could not send http response");
                unsent_chunk = Some(chunk);
                Ok(Async::NotReady)
            }
        }
    }))
}

// Next we define some record types which are marshalled to and from gluon. These have equivalent
// definitions in http_types.glu
field_decl! { method, uri, status, body, request, response }

type Request = record_type!{
    method => String,
    uri => String,
    body => Body
};

type Response = record_type!{
    status => u16
};

type HttpState = record_type!{
    request => Request,
    response => ResponseBody
};

fn listen(
    port: i32,
    value: WithVM<OpaqueValue<RootedThread, Handler<Response>>>,
) -> FutureResult<impl Future<Item = IO<()>, Error = vm::Error> + Send + 'static> {
    let WithVM {
        value: handler,
        vm: thread,
    } = value;

    let thread = match thread.new_thread() {
        Ok(thread) => thread,
        Err(err) => return FutureResult(Either::A(future::err(err))),
    };

    // Retrieve the `handle` function from the http module which we use to evaluate values of type
    // `Handler Response`
    type ListenFn = fn(OpaqueValue<RootedThread, Handler<Response>>, HttpState) -> IO<Response>;
    let handle: Function<RootedThread, ListenFn> = thread
        .get_global("examples.http.http.handle")
        .unwrap_or_else(|err| panic!("{}", err));

    struct Listen {
        handle: Function<RootedThread, ListenFn>,
        handler: OpaqueValue<RootedThread, Handler<Response>>,
    }

    impl Service for Listen {
        type ReqBody = hyper::Body;
        type ResBody = hyper::Body;
        type Error = hyper::Error;
        type Future =
            Box<Future<Item = http::Response<hyper::Body>, Error = hyper::Error> + Send + 'static>;

        fn call(&mut self, request: http::Request<hyper::Body>) -> Self::Future {
            let gluon_request = record_no_decl! {
                method => request.method().as_str().to_owned(),
                uri => request.uri().to_string(),
                // Since `Body` implements `Userdata` it can be directly pushed to gluon
                body => Body(Arc::new(Mutex::new(Box::new(request.into_body()
                    .map_err(|err| VmError::Message(format!("{}", err)))
                    // `PushAsRef` makes the `body` parameter act as a `&[u8]` which means it is
                    // marshalled to `Array Byte` in gluon
                    .map(PushAsRef::<_, [u8]>::new)))))
            };
            let (response_sender, response_body) = hyper::Body::channel();
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

                                    let status = StatusCode::from_u16(status).unwrap_or(StatusCode::INTERNAL_SERVER_ERROR);
                                    Ok(
                                        http::Response::builder()
                                            .status(status)
                                            .body(response_body).unwrap(),
                                    )
                                }
                                IO::Exception(err) => {
                                    eprintln!("{}", err);
                                    Ok(
                                        http::Response::builder()
                                            .status(StatusCode::INTERNAL_SERVER_ERROR).body("".into()).unwrap()
                                    )
                                }
                            }
                        }
                        Err(err) => {
                            eprintln!("{}", err);
                            Ok(http::Response::builder()
                                .status(StatusCode::INTERNAL_SERVER_ERROR)
                                .body("".into())
                                .unwrap())
                        }
                    }),
            )
        }
    }

    let addr = format!("127.0.0.1:{}", port).parse().unwrap();

    let (sender, receiver) = oneshot::channel();
    tokio::spawn(
        Server::bind(&addr)
            .serve(move || -> Result<_, hyper::Error> {
                Ok(Listen {
                    handle: handle.clone(),
                    handler: handler.clone(),
                })
            })
            .map_err(|err| {
                error!("{}", err);
            })
            .and_then(|_| sender.send(IO::Value(())).map_err(|_| ())),
    );
    FutureResult(Either::B(
        receiver.map_err(|err| vm::Error::from(format!("Server error: {}", err))),
    ))
}

// To let the `http_types` module refer to `Body` and `ResponseBody` we register these types in a
// separate function which is called before loading `http_types`
pub fn load_types(vm: &Thread) -> VmResult<ExternModule> {
    vm.register_type::<Body>("Body", &[])?;
    vm.register_type::<ResponseBody>("ResponseBody", &[])?;

    ExternModule::new(
        vm,
        record! {
            // Define the types so that they can be used from gluon
            type Body => Body,
            type ResponseBody => ResponseBody,
            type Method => String,
            type StatusCode => u16,
            type Request => Request,
            type Response => Response,
            type HttpState => HttpState
        },
    )
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
    env_logger::init();

    let port = env::args()
        .nth(1)
        .map(|port| port.parse::<u16>().expect("port"))
        .unwrap_or(80);

    let thread = new_vm();
    tokio::run(start(&thread, port).map_err(|err| panic!("{}", err)));
}

fn start(
    thread: &Thread,
    port: u16,
) -> impl Future<Item = (), Error = Box<StdError + Send + Sync + 'static>> {
    add_extern_module(&thread, "http.prim_types", load_types);
    add_extern_module(&thread, "http.prim", load);

    let thread = thread.root_thread();
    future::lazy(|| -> Result<_, Box<StdError + Send + Sync>> {
        // Last we run our `http_server.glu` module which returns a function which starts listening
        // on the port we passed from the command line
        let mut expr = String::new();
        {
            let mut file = File::open("examples/http/server.glu")?;
            file.read_to_string(&mut expr)?;
        }
        Ok(expr)
    }).and_then(move |expr| {
        Compiler::new()
            .run_expr_async::<OwnedFunction<fn(u16) -> IO<()>>>(
                &thread,
                "examples/http/server.glu",
                &expr,
            )
            .from_err()
            .and_then(move |(mut listen, _)| {
                FutureValue::Future(listen.call_async(port))
                    .from_err()
                    .map(|_| ())
            })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate tokio_retry;

    use std::str;

    use hyper::Client;

    use tokio::runtime::Runtime;

    #[test]
    fn hello_world() {
        let mut runtime = Runtime::new().unwrap();

        let port = 1222;
        let thread = new_vm();

        runtime.spawn(start(&thread, port).map_err(|err| panic!("{}", err)));

        let future =
            move || Client::new().get(format!("http://localhost:{}", port).parse().unwrap());

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(10);

        runtime
            .block_on(
                tokio_retry::Retry::spawn(retry_strategy, future)
                    .map_err(|err| panic!("{}", err))
                    .and_then(|response| {
                        response.into_body().concat2().map(|body| {
                            assert_eq!(str::from_utf8(&body).unwrap(), "Hello World");
                        })
                    }),
            )
            .unwrap();
    }

    #[test]
    fn echo() {
        let mut runtime = Runtime::new().unwrap();

        let port = 1223;
        let thread = new_vm();
        runtime.spawn(start(&thread, port).map_err(|err| panic!("{}", err)));

        let future = move || {
            let request = hyper::Request::post(format!("http://localhost:{}/echo", port))
                .body(hyper::Body::from("test"))
                .unwrap();

            Client::new().request(request)
        };

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(10);

        runtime
            .block_on(
                tokio_retry::Retry::spawn(retry_strategy, future)
                    .map_err(|err| panic!("{}", err))
                    .and_then(|response| {
                        response.into_body().concat2().map(|body| {
                            assert_eq!(str::from_utf8(&body).unwrap(), "test");
                        })
                    }),
            )
            .unwrap();
    }
}
