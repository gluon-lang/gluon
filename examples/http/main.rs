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
extern crate tokio_core;
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;

use std::env;
use std::error::Error as StdError;
use std::fmt;
use std::fs::File;
use std::io::{stderr, Read, Write};
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

use hyper::server::Service;
use hyper::{Chunk, Method, StatusCode};

use futures::future::Either;
use futures::sink::Sink;
use futures::stream::Stream;
use futures::sync::mpsc::Sender;
use futures::sync::oneshot;
use futures::{future, Async, Future};

use tokio_core::reactor::Core;

use base::types::{ArcType, Type};

use vm::{Error as VmError, ExternModule, Result as VmResult};

use gluon::import::add_extern_module;
use vm::api::{
    Function, FutureResult, Getable, OpaqueValue, OwnedFunction, PushAsRef, Pushable, Userdata,
    VmType, WithVM, IO,
};
use vm::future::FutureValue;
use vm::gc::{Gc, Traverseable};
use vm::thread::{Context, RootedThread, Thread};
use vm::Variants;

use gluon::{Compiler, VmBuilder};

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

// Rust does not let us define traits on types defined in a different crate such as `hyper`. We can
// however work around this by defining a wrapper type which we are then able to define the traits
// on.
struct Wrap<T>(T);

macro_rules! define_vmtype {
    ($name:ident, $wrapper:ident) => {
        impl VmType for Wrap<$name> {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                $wrapper::make_type(vm)
            }
        }

        impl VmType for $wrapper {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                use gluon::base::types::Alias;

                // If we have already created $name then return it immediately
                if let Some(typ) = vm.get_type::<$name>() {
                    return typ;
                }

                // Otherwise construct the type using the `Deserialize` impl for the type
                let (name, typ) = gluon::vm::api::typ::from_rust::<Self>(vm).unwrap();
                vm.register_type_as(
                    name.clone(),
                    Alias::new(name, typ),
                    ::std::any::TypeId::of::<$name>(),
                ).unwrap()
            }
        }
    };
}

// This type, and the `StatusCode` type below are defined in hyper so we can't implement any traits
// on them. Instead we use serde's remote derive support to workaround it.
#[derive(Serialize, Deserialize)]
#[serde(remote = "Method")]
#[serde(rename = "Method")]
pub enum RemoteMethod {
    Options,
    Get,
    Post,
    Put,
    Delete,
    Head,
    Trace,
    Connect,
    Patch,
    Extension(String),
}
#[derive(Serialize, Deserialize)]
struct RemoteMethodContainer(#[serde(with = "RemoteMethod")] Method);

define_vmtype! { Method, RemoteMethodContainer }

impl<'vm> Pushable<'vm> for Wrap<Method> {
    fn push(self, vm: &'vm Thread, context: &mut Context) -> VmResult<()> {
        use gluon::vm::api::ser::Ser;
        Ser(RemoteMethodContainer(self.0)).push(vm, context)
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "StatusCode")]
#[serde(rename = "StatusCode")]
pub enum RemoteStatusCode {
    Continue,
    SwitchingProtocols,
    Processing,
    Ok,
    Created,
    Accepted,
    NonAuthoritativeInformation,
    NoContent,
    ResetContent,
    PartialContent,
    MultiStatus,
    AlreadyReported,
    ImUsed,
    MultipleChoices,
    MovedPermanently,
    Found,
    SeeOther,
    NotModified,
    UseProxy,
    TemporaryRedirect,
    PermanentRedirect,
    BadRequest,
    Unauthorized,
    PaymentRequired,
    Forbidden,
    NotFound,
    MethodNotAllowed,
    NotAcceptable,
    ProxyAuthenticationRequired,
    RequestTimeout,
    Conflict,
    Gone,
    LengthRequired,
    PreconditionFailed,
    PayloadTooLarge,
    UriTooLong,
    UnsupportedMediaType,
    RangeNotSatisfiable,
    ExpectationFailed,
    ImATeapot,
    MisdirectedRequest,
    UnprocessableEntity,
    Locked,
    FailedDependency,
    UpgradeRequired,
    PreconditionRequired,
    TooManyRequests,
    RequestHeaderFieldsTooLarge,
    UnavailableForLegalReasons,
    InternalServerError,
    NotImplemented,
    BadGateway,
    ServiceUnavailable,
    GatewayTimeout,
    HttpVersionNotSupported,
    VariantAlsoNegotiates,
    InsufficientStorage,
    LoopDetected,
    NotExtended,
    NetworkAuthenticationRequired,
    Unregistered(u16),
}
#[derive(Serialize, Deserialize)]
struct StatusCodeContainer(#[serde(with = "RemoteStatusCode")] StatusCode);

define_vmtype! { StatusCode, StatusCodeContainer }

impl<'vm, 'value> Getable<'vm, 'value> for Wrap<StatusCode> {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        use gluon::vm::api::de::De;
        Wrap((De::<StatusCodeContainer>::from_value(vm, value).0).0)
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

fn listen(
    port: i32,
    value: WithVM<OpaqueValue<RootedThread, Handler<Response>>>,
) -> FutureResult<impl Future<Item = IO<()>, Error = vm::Error> + Send + 'static> {
    let WithVM {
        value: handler,
        vm: thread,
    } = value;

    use hyper::server::{Http, Request as HyperRequest, Response as HyperResponse};

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

    let (sender, receiver) = oneshot::channel();
    thread
        .get_event_loop()
        .expect("event loop")
        .spawn(move |h| {
            let h = h.clone();
            future::result(Http::new().serve_addr_handle(&addr, &h, move || {
                Ok(Listen {
                    handle: handle.clone(),
                    handler: handler.clone(),
                })
            })).flatten_stream()
                .for_each(move |con| {
                    h.spawn(con.map(|_| ()).map_err(|err| error!("{}", err)));
                    Ok(())
                })
                .map_err(|err| {
                    error!("{}", err);
                })
                .and_then(|_| sender.send(IO::Value(())).map_err(|_| ()))
        });
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
            type Method => Wrap<Method>,
            type StatusCode => Wrap<StatusCode>,
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

    let mut core = Core::new().unwrap();

    let thread = VmBuilder::new().event_loop(Some(core.remote())).build();
    let result = core.run(start(&thread, port));
    if let Err(err) = result {
        panic!("{}", err)
    }
}

fn start(thread: &Thread, port: u16) -> impl Future<Item = (), Error = Box<StdError + 'static>> {
    add_extern_module(&thread, "http.prim_types", load_types);
    add_extern_module(&thread, "http.prim", load);

    let thread = thread.root_thread();
    future::lazy(|| -> Result<_, Box<StdError>> {
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

    use std::str;

    use hyper::Client;

    #[test]
    fn hello_world() {
        let mut core = Core::new().unwrap();

        let port = 1222;
        let thread = VmBuilder::new().event_loop(Some(core.remote())).build();
        core.handle()
            .spawn(start(&thread, port).map_err(|err| panic!("{}", err)));

        let handle = core.handle();
        core.run(
            Client::new(&handle)
                .get(format!("http://localhost:{}", port).parse().unwrap())
                .and_then(|response| {
                    response.body().concat2().map(|body| {
                        assert_eq!(str::from_utf8(&body).unwrap(), "Hello World");
                    })
                }),
        ).unwrap();
    }

    #[test]
    fn echo() {
        let mut core = Core::new().unwrap();

        let port = 1223;
        let thread = VmBuilder::new().event_loop(Some(core.remote())).build();
        core.handle()
            .spawn(start(&thread, port).map_err(|err| panic!("{}", err)));

        let handle = core.handle();

        let mut request = hyper::Request::new(
            Method::Post,
            format!("http://localhost:{}/echo", port).parse().unwrap(),
        );
        request.set_body(hyper::Body::from("test"));
        core.run(Client::new(&handle).request(request).and_then(|response| {
            response.body().concat2().map(|body| {
                assert_eq!(str::from_utf8(&body).unwrap(), "test");
            })
        })).unwrap();
    }
}
