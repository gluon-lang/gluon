extern crate http;
extern crate hyper;
extern crate native_tls;
extern crate tokio_tcp;
extern crate tokio_tls;

use std::{
    fmt, fs,
    path::Path,
    sync::{Arc, Mutex},
};

use self::{http::StatusCode, hyper::service::Service, hyper::Chunk, hyper::Server};

use futures::{
    future::{self, Either},
    Async, Future, Stream,
};

use self::http::header::{HeaderMap, HeaderName, HeaderValue};

use base::types::{ArcType, Type};

use vm::{
    self,
    api::{
        generic, Collect, Eff, Function, Getable, OpaqueValue, PushAsRef, Pushable, VmType, WithVM,
        IO,
    },
    thread::{ActiveThread, RootedThread, Thread},
    ExternModule, Variants,
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

struct HttpEffect;
impl VmType for HttpEffect {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        let r = generic::R::make_type(vm);
        Type::app(
            vm.find_type_info("std.http.types.HttpEffect")
                .map(|alias| alias.into_type())
                .unwrap_or_else(|_| Type::hole()),
            collect![r],
        )
    }
}

type Handler<T> = Eff<HttpEffect, T>;

struct Headers(HeaderMap);

impl VmType for Headers {
    type Type = Vec<(String, Vec<u8>)>;

    fn make_type(vm: &Thread) -> ArcType {
        Vec::<(String, Vec<u8>)>::make_type(vm)
    }
}

impl<'vm> Pushable<'vm> for Headers {
    fn push(self, context: &mut ActiveThread<'vm>) -> vm::Result<()> {
        Collect::new(
            self.0
                .iter()
                .map(|(name, value)| (name.as_str(), value.as_bytes())),
        )
        .push(context)
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for Headers {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        Headers(
            Collect::from_value(vm, value)
                // TODO Error somehow on invalid headers
                .filter_map(|(name, value): (&str, &[u8])| {
                    match (HeaderName::from_bytes(name.as_bytes()), HeaderValue::from_bytes(value)) {
                        (Ok(name), Ok(value)) => Some((name, value)),
                        _ => None,
                    }
                })
                .collect(),
        )
    }
}

// By implementing `Userdata` on `Body` it can be automatically pushed and retrieved from gluon
// threads
#[derive(Userdata)]
#[gluon(crate_name = "::vm")]
// Representation of a http body that is in the prograss of being read
pub struct Body(Arc<Mutex<Box<Stream<Item = PushAsRef<Chunk, [u8]>, Error = vm::Error> + Send>>>);

// Types implementing `Userdata` requires a `std::fmt::Debug` implementation so it can be displayed
impl fmt::Debug for Body {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "hyper::Body")
    }
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
#[derive(Userdata)]
#[gluon(crate_name = "::vm")]
pub struct ResponseBody(Arc<Mutex<Option<hyper::body::Sender>>>);

impl fmt::Debug for ResponseBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "hyper::Response")
    }
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

#[derive(Debug, Userdata)]
#[gluon(crate_name = "::vm")]
struct Uri(http::Uri);

// Next we define some record types which are marshalled to and from gluon. These have equivalent
// definitions in http_types.glu
field_decl! { http, method, uri, status, body, request, response, headers }

type Request = record_type! {
    method => String,
    uri => Uri,
    body => Body
};

type Response = record_type! {
    status => u16,
    headers => Headers
};

type HttpState = record_type! {
    request => Request,
    response => ResponseBody
};

#[derive(Getable, VmType)]
#[gluon(crate_name = "::vm")]
struct Settings<'a> {
    port: u16,
    tls_cert: Option<&'a Path>,
}

fn listen(
    settings: Settings,
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
            let (parts, body) = request.into_parts();
            let gluon_request = record_no_decl! {
                method => parts.method.as_str().to_owned(),
                uri => Uri(parts.uri),
                // Since `Body` implements `Userdata` it can be directly pushed to gluon
                body => Body(Arc::new(Mutex::new(Box::new(body
                    .map_err(|err| vm::Error::Message(format!("{}", err)))
                    // `PushAsRef` makes the `body` parameter act as a `&[u8]` which means it is
                    // marshalled to `Array Byte` in gluon
                    .map(PushAsRef::<_, [u8]>::new)))))
            };
            let (response_sender, response_body) = hyper::Body::channel();
            let response_sender = Arc::new(Mutex::new(Some(response_sender)));
            let http_state = record_no_decl! {
                request => gluon_request,
                response => ResponseBody(response_sender.clone())
            };

            let child_thread = try_future!(self.handle.vm().new_thread());
            let mut handle = try_future!(self.handle.re_root(child_thread));

            Box::new(
                handle.call_async(self.handler.clone(), http_state).then(
                    move |result| match result {
                        Ok(value) => {
                            match value {
                                IO::Value(record_p! { status, headers }) => {
                                    // Drop the sender to so that it the receiver stops waiting for
                                    // more chunks
                                    *response_sender.lock().unwrap() = None;

                                    let status = StatusCode::from_u16(status)
                                        .unwrap_or(StatusCode::INTERNAL_SERVER_ERROR);
                                    let mut response = http::Response::builder()
                                        .status(status)
                                        .body(response_body)
                                        .unwrap();
                                    *response.headers_mut() = headers.0;
                                    Ok(response)
                                }
                                IO::Exception(err) => {
                                    error!("{}", err);
                                    Ok(http::Response::builder()
                                        .status(StatusCode::INTERNAL_SERVER_ERROR)
                                        .body("".into())
                                        .unwrap())
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
                    },
                ),
            )
        }
    }

    let addr = format!("0.0.0.0:{}", settings.port).parse().unwrap();

    if let Some(cert_path) = settings.tls_cert {
        let identity = try_future!(
            fs::read(cert_path).map_err(|err| vm::Error::Message(format!(
                "Unable to open certificate `{}`: {}",
                cert_path.display(),
                err
            ))),
            Either::A
        );

        let identity = try_future!(
            native_tls::Identity::from_pkcs12(&identity, "")
                .map_err(|err| vm::Error::Message(err.to_string())),
            Either::A
        );
        let acceptor = tokio_tls::TlsAcceptor::from(try_future!(
            native_tls::TlsAcceptor::new(identity)
                .map_err(|err| vm::Error::Message(err.to_string())),
            Either::A
        ));

        let http = hyper::server::conn::Http::new();
        let listener = try_future!(
            tokio_tcp::TcpListener::bind(&addr).map_err(|err| vm::Error::Message(err.to_string())),
            Either::A
        );
        let incoming = listener
            .incoming()
            .and_then(move |stream| {
                acceptor.accept(stream).map(Some).or_else(|err| {
                    info!("Unable to accept TLS connection: {}", err);
                    Ok(None)
                })
            })
            .filter_map(|opt_tls_stream| opt_tls_stream);

        let future = http
            .serve_incoming(incoming, move || -> Result<_, hyper::Error> {
                Ok(Listen {
                    handle: handle.clone(),
                    handler: handler.clone(),
                })
            })
            .and_then(|connecting| connecting)
            .for_each(|connection| {
                hyper::rt::spawn(connection.map_err(|err| error!("{}", err)));
                Ok(())
            })
            .map(|_| IO::Value(()))
            .map_err(|err| vm::Error::from(format!("Server error: {}", err)));
        return Either::B(Either::A(future));
    }

    Either::B(Either::B(
        Server::bind(&addr)
            .serve(move || -> Result<_, hyper::Error> {
                Ok(Listen {
                    handle: handle.clone(),
                    handler: handler.clone(),
                })
            })
            .map_err(|err| vm::Error::from(format!("Server error: {}", err)))
            .map(|_| IO::Value(())),
    ))
}

// To let the `http_types` module refer to `Body` and `ResponseBody` we register these types in a
// separate function which is called before loading `http_types`
pub fn load_types(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<Body>("Body", &[])?;
    vm.register_type::<ResponseBody>("ResponseBody", &[])?;
    vm.register_type::<Uri>("Uri", &[])?;

    ExternModule::new(
        vm,
        record! {
            // Define the types so that they can be used from gluon
            type Body => Body,
            type ResponseBody => ResponseBody,
            type Uri => Uri,
            type Method => String,
            type StatusCode => u16,
            type Request => Request,
            type Response => Response,
            type Headers => Headers,
            type HttpState => HttpState
        },
    )
}

macro_rules! uri_binds {
    ($($id: ident)*) => {
        record!{
            $(
                $id => primitive!(1, concat!("std.http.prim.uri.", stringify!($id)), |u: &Uri| (u.0).$id())
            ),*
        }
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            listen => primitive!(2, async fn listen),
            read_chunk => primitive!(1, async fn read_chunk),
            write_response => primitive!(2, async fn write_response),
            port => primitive!(1, "std.http.prim.uri.port", |u: &Uri| (u.0).port_part().map(|p| p.as_u16())),
            uri => uri_binds!(path host query to_string)
        },
    )
}
