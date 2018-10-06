extern crate http;
extern crate hyper;

use std::fmt;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};

use self::{http::StatusCode, hyper::service::Service, hyper::Chunk, hyper::Server};

use futures::future::Either;
use futures::stream::Stream;
use futures::{future, Async, Future};

use base::types::{ArcType, Type};

use vm::{
    self,
    api::{Function, OpaqueValue, PushAsRef, Userdata, VmType, WithVM, IO},
    gc::{Gc, Traverseable},
    thread::{RootedThread, Thread},
    ExternModule,
};

macro_rules! try_future {
    ($e:expr) => {
        try_future!($e, Box::new)
    };
    ($e:expr, $f:expr) => {
        match $e {
            Ok(x) => x,
            Err(err) => return $f(::futures::future::err(err.into())),
        }
    };
}

mod std {
    pub use http;
}

// `Handler` is a type defined in http.glu but since we need to refer to it in the signature of
// listen we define a phantom type which we can use with `OpaqueValue` to store a `Handler` in Rust
struct Handler<T>(PhantomData<T>);

impl<T: VmType + 'static> VmType for Handler<T> {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        vm.find_type_info("std.http.types.Handler")
            .map(|typ| Type::app(typ.into_type(), collect![T::make_type(vm)]))
            .unwrap_or_else(|_| Type::hole())
    }
}

// Representation of a http body that is in the prograss of being read
pub struct Body(Arc<Mutex<Box<Stream<Item = PushAsRef<Chunk, [u8]>, Error = vm::Error> + Send>>>);

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
) -> impl Future<Item = IO<Option<PushAsRef<Chunk, [u8]>>>, Error = vm::Error> {
    use futures::future::poll_fn;

    let body = body.0.clone();
    poll_fn(move || {
        let mut stream = body.lock().unwrap();
        stream.poll().map(|async| async.map(IO::Value))
    })
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
) -> impl Future<Item = IO<()>, Error = vm::Error> {
    use futures::future::poll_fn;

    // Turn `bytes´ into a `Chunk` which can be sent to the http body
    let mut unsent_chunk = Some(bytes.to_owned().into());
    let response = response.0.clone();
    poll_fn(move || {
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
    })
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
) -> impl Future<Item = IO<()>, Error = vm::Error> + Send + 'static {
    let WithVM {
        value: handler,
        vm: thread,
    } = value;

    let thread = match thread.new_thread() {
        Ok(thread) => thread,
        Err(err) => return Either::A(future::err(err)),
    };

    // Retrieve the `handle` function from the http module which we use to evaluate values of type
    // `Handler Response`
    type ListenFn = fn(OpaqueValue<RootedThread, Handler<Response>>, HttpState) -> IO<Response>;
    let handle: Function<RootedThread, ListenFn> = thread
        .get_global("std.http.http.handle")
        .unwrap_or_else(|err| panic!("{}", err));

    struct Listen {
        handle: Function<RootedThread, ListenFn>,
        handler: OpaqueValue<RootedThread, Handler<Response>>,
    }

    impl Service for Listen {
        type ReqBody = hyper::Body;
        type ResBody = hyper::Body;
        type Error = vm::Error;
        type Future =
            Box<Future<Item = http::Response<hyper::Body>, Error = Self::Error> + Send + 'static>;

        fn call(&mut self, request: http::Request<hyper::Body>) -> Self::Future {
            let gluon_request = record_no_decl! {
                method => request.method().as_str().to_owned(),
                uri => request.uri().to_string(),
                // Since `Body` implements `Userdata` it can be directly pushed to gluon
                body => Body(Arc::new(Mutex::new(Box::new(request.into_body()
                    .map_err(|err| vm::Error::Message(format!("{}", err)))
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

            let child_thread = try_future!(self.handle.vm().new_thread());
            let mut handle = try_future!(self.handle.re_root(child_thread));

            Box::new(
                handle
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
                                    error!("{}", err);
                                    Ok(
                                        http::Response::builder()
                                            .status(StatusCode::INTERNAL_SERVER_ERROR).body("".into()).unwrap()
                                    )
                                }
                            }
                        }
                        Err(err) => {
                            error!("{}", err);
                            Ok(http::Response::builder()
                                .status(StatusCode::INTERNAL_SERVER_ERROR)
                                .body("".into())
                                .unwrap())
                        }
                    }),
            )
        }
    }

    let addr = format!("0.0.0.0:{}", port).parse().unwrap();

    Either::B(
        Server::bind(&addr)
            .serve(move || -> Result<_, hyper::Error> {
                Ok(Listen {
                    handle: handle.clone(),
                    handler: handler.clone(),
                })
            }).map_err(|err| vm::Error::from(format!("Server error: {}", err)))
            .and_then(|_| Ok(IO::Value(()))),
    )
}

// To let the `http_types` module refer to `Body` and `ResponseBody` we register these types in a
// separate function which is called before loading `http_types`
pub fn load_types(vm: &Thread) -> vm::Result<ExternModule> {
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

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            listen => primitive!(2, async fn listen),
            read_chunk => primitive!(1, async fn read_chunk),
            write_response => primitive!(2, async fn write_response)
        },
    )
}
