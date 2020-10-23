use crate::real_std::{
    fmt, fs,
    path::PathBuf,
    pin::Pin,
    sync::{Arc, Mutex},
};

use {
    collect_mac::collect,
    futures::{
        future::{self, BoxFuture},
        prelude::*,
        ready,
        task::{self, Poll},
    },
    http::{
        header::{HeaderMap, HeaderName, HeaderValue},
        StatusCode,
    },
    hyper::{body::Bytes, Server},
    pin_project_lite::pin_project,
};

use crate::base::types::{ArcType, Type};

use crate::{
    vm::{
        self,
        api::{
            generic, Collect, Eff, Function, Getable, OpaqueValue, PushAsRef, Pushable, VmType,
            WithVM, IO,
        },
        thread::{ActiveThread, RootedThread, Thread},
        ExternModule, Variants,
    },
    Error,
};

macro_rules! try_future {
    ($e:expr) => {
        try_future!($e, Box::pin)
    };
    ($e:expr, $f:expr) => {
        match $e {
            Ok(x) => x,
            Err(err) => return $f(::futures::future::err(err.into())),
        }
    };
}

pub struct HttpEffect;
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

pub type EffectHandler<T> = Eff<HttpEffect, T>;

pub struct Headers(HeaderMap);

impl VmType for Headers {
    type Type = Vec<(String, Vec<u8>)>;

    fn make_type(vm: &Thread) -> ArcType {
        Vec::<(String, Vec<u8>)>::make_type(vm)
    }
}

impl<'vm> Pushable<'vm> for Headers {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> vm::Result<()> {
        Collect::new(
            self.0
                .iter()
                .map(|(name, value)| (name.as_str(), value.as_bytes())),
        )
        .vm_push(context)
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for Headers {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        Headers(
            Collect::from_value(vm, value)
                // TODO Error somehow on invalid headers
                .filter_map(|(name, value): (&str, &[u8])| {
                    match (
                        HeaderName::from_bytes(name.as_bytes()),
                        HeaderValue::from_bytes(value),
                    ) {
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
#[derive(Userdata, Trace, VmType, Clone)]
#[gluon(vm_type = "std.http.types.Body")]
#[gluon(crate_name = "::vm")]
#[gluon_userdata(clone)]
#[gluon_trace(skip)]
// Representation of a http body that is in the prograss of being read
pub struct Body(
    Arc<Mutex<Pin<Box<dyn Stream<Item = Result<PushAsRef<Bytes, [u8]>, vm::Error>> + Send>>>>,
);

// Types implementing `Userdata` requires a `std::fmt::Debug` implementation so it can be displayed
impl fmt::Debug for Body {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "hyper::Body")
    }
}

// Since `Body` implements `Userdata` gluon will automatically marshal the gluon representation
// into `&Body` argument
fn read_chunk(body: &Body) -> impl Future<Output = IO<Option<PushAsRef<Bytes, [u8]>>>> {
    use futures::future::poll_fn;

    let body = body.0.clone();
    poll_fn(move |cx| {
        let mut stream = body.lock().unwrap();
        Poll::Ready(IO::Value(
            if let Some(result) = ready!(stream.as_mut().poll_next(cx)) {
                match result {
                    Ok(chunk) => Some(chunk),
                    Err(err) => return IO::Exception(err.to_string()).into(),
                }
            } else {
                None
            },
        ))
    })
}

// A http body that is being written
#[derive(Userdata, Trace, VmType, Clone)]
#[gluon(vm_type = "std.http.types.ResponseBody")]
#[gluon(crate_name = "::vm")]
#[gluon_userdata(clone)]
#[gluon_trace(skip)]
pub struct ResponseBody(Arc<Mutex<Option<hyper::body::Sender>>>);

impl fmt::Debug for ResponseBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ResponseBody")
    }
}

fn write_response(response: &ResponseBody, bytes: &[u8]) -> impl Future<Output = IO<()>> {
    use futures::future::poll_fn;

    // Turn `bytes´ into a `Bytes` which can be sent to the http body
    let mut unsent_chunk = Some(bytes.to_owned().into());
    let response = response.0.clone();
    poll_fn(move |cx| {
        info!("Starting response send");
        let mut sender = response.lock().unwrap();
        let sender = sender
            .as_mut()
            .expect("Sender has been dropped while still in use");
        let chunk = unsent_chunk
            .take()
            .expect("Attempt to poll after chunk is sent");
        match sender.poll_ready(cx) {
            Poll::Pending => {
                unsent_chunk = Some(chunk);
                return Poll::Pending;
            }
            Poll::Ready(Ok(_)) => (),
            Poll::Ready(Err(err)) => {
                info!("Could not send http response {}", err);
                return IO::Exception(err.to_string()).into();
            }
        }
        match sender.try_send_data(chunk) {
            Ok(()) => Poll::Ready(IO::Value(())),
            Err(chunk) => {
                unsent_chunk = Some(chunk);
                IO::Exception("Could not send http response".into()).into()
            }
        }
    })
}

#[derive(Debug, Userdata, Trace, VmType, Clone)]
#[gluon(vm_type = "std.http.types.Uri")]
#[gluon(crate_name = "::vm")]
#[gluon_trace(skip)]
#[gluon_userdata(clone)]
struct Uri(http::Uri);

// Next we define some record types which are marshalled to and from gluon. These have equivalent
// definitions in http_types.glu
field_decl! { http, method, uri, status, body, request, response, headers }

type Request = record_type! {
    method => String,
    uri => Uri,
    body => Body
};

pub type Response = record_type! {
    status => u16,
    headers => Headers
};

type HttpState = record_type! {
    request => Request,
    response => ResponseBody
};

#[derive(Getable, VmType)]
#[gluon(crate_name = "::vm")]
struct Settings {
    port: u16,
    tls_cert: Option<PathBuf>,
}

fn listen(
    settings: Settings,
    WithVM { vm, value }: WithVM<OpaqueValue<RootedThread, EffectHandler<Response>>>,
) -> impl Future<Output = IO<()>> + Send + 'static {
    let vm = vm.root_thread();
    listen_(settings, vm, value).map(IO::from)
}

async fn listen_(
    settings: Settings,
    thread: RootedThread,
    handler: OpaqueValue<RootedThread, EffectHandler<Response>>,
) -> vm::Result<()> {
    let thread = match thread.new_thread() {
        Ok(thread) => thread,
        Err(err) => return Err(err),
    };

    impl tower_service::Service<hyper::Request<hyper::Body>> for Handler {
        type Response = hyper::Response<hyper::Body>;
        type Error = Error;
        type Future = BoxFuture<'static, Result<http::Response<hyper::Body>, Error>>;

        fn poll_ready(&mut self, _cx: &mut task::Context<'_>) -> Poll<Result<(), Self::Error>> {
            Ok(()).into()
        }

        fn call(&mut self, request: hyper::Request<hyper::Body>) -> Self::Future {
            let (parts, body) = request.into_parts();
            self.handle(parts.method, parts.uri, body)
        }
    }

    let addr = format!("0.0.0.0:{}", settings.port).parse().unwrap();

    let listener = Handler::new(&thread, handler);

    if let Some(cert_path) = &settings.tls_cert {
        let identity = fs::read(cert_path).map_err(|err| {
            vm::Error::Message(format!(
                "Unable to open certificate `{}`: {}",
                cert_path.display(),
                err
            ))
        })?;

        let identity = native_tls::Identity::from_pkcs12(&identity, "")
            .map_err(|err| vm::Error::Message(err.to_string()))?;
        let acceptor = tokio_native_tls::TlsAcceptor::from(
            native_tls::TlsAcceptor::new(identity)
                .map_err(|err| vm::Error::Message(err.to_string()))?,
        );

        let http = hyper::server::conn::Http::new();

        let mut tcp_listener = tokio::net::TcpListener::bind(&addr)
            .map_err(|err| vm::Error::Message(err.to_string()))
            .await?;
        let incoming = tcp_listener.incoming().err_into().and_then(|stream| {
            acceptor.accept(stream).map_err(|err| {
                info!("Unable to accept TLS connection: {}", err);
                Box::new(err) as Box<dyn ::std::error::Error + Send + Sync>
            })
        });

        pin_project! {
            struct Acceptor<S> {
                #[pin]
                incoming: S,
            }
        }
        impl<S, T, E> hyper::server::accept::Accept for Acceptor<S>
        where
            S: Stream<Item = Result<T, E>>,
        {
            type Conn = T;
            type Error = E;
            fn poll_accept(
                self: Pin<&mut Self>,
                cx: &mut task::Context<'_>,
            ) -> Poll<Option<Result<Self::Conn, Self::Error>>> {
                self.project().incoming.poll_next(cx)
            }
        }

        return hyper::server::Builder::new(Acceptor { incoming }, http)
            .serve(hyper::service::make_service_fn(move |_| {
                future::ready(Ok::<_, hyper::Error>(listener.clone()))
            }))
            .map_err(|err| vm::Error::from(format!("Server error: {}", err)))
            .await;
    }

    Server::bind(&addr)
        .serve(hyper::service::make_service_fn(move |_| {
            future::ready(Ok::<_, hyper::Error>(listener.clone()))
        }))
        .map_err(|err| vm::Error::from(format!("Server error: {}", err)))
        .map_ok(|_| ())
        .await
}

type ListenFn = fn(OpaqueValue<RootedThread, EffectHandler<Response>>, HttpState) -> IO<Response>;

#[derive(Clone)]
pub struct Handler {
    handle: Function<RootedThread, ListenFn>,
    handler: OpaqueValue<RootedThread, EffectHandler<Response>>,
}

impl Handler {
    pub fn new(
        thread: &Thread,
        handler: OpaqueValue<RootedThread, EffectHandler<Response>>,
    ) -> Self {
        // Retrieve the `handle` function from the http module which we use to evaluate values of type
        // `EffectHandler Response`
        let handle: Function<RootedThread, ListenFn> = thread
            .get_global("std.http.handle")
            .unwrap_or_else(|err| panic!("{}", err));
        Self { handle, handler }
    }

    pub fn handle<E>(
        &mut self,
        method: http::Method,
        uri: http::Uri,
        body: impl Stream<Item = Result<Bytes, E>> + Send + 'static,
    ) -> BoxFuture<'static, crate::Result<hyper::Response<hyper::Body>>>
    where
        E: fmt::Display + Send + 'static,
    {
        let child_thread = try_future!(self.handle.vm().new_thread());
        let mut handle = try_future!(self.handle.re_root(child_thread));

        let gluon_request = record_no_decl! {
            method => method.as_str().to_owned(),
            uri => Uri(uri),
            // Since `Body` implements `Userdata` it can be directly pushed to gluon
            body => Body(Arc::new(Mutex::new(Box::pin(
                body
                    .map_err(|err| vm::Error::Message(format!("{}", err)))
                    // `PushAsRef` makes the `body` parameter act as a `&[u8]` which means it is
                    // marshalled to `Array Byte` in gluon
                    .map_ok(PushAsRef::<_, [u8]>::new)
            ))))
        };
        let (response_sender, response_body) = hyper::Body::channel();
        let response_sender = Arc::new(Mutex::new(Some(response_sender)));
        let http_state = record_no_decl! {
            request => gluon_request,
            response => ResponseBody(response_sender.clone())
        };

        let handler = self.handler.clone();
        Box::pin(async move {
            handle
                .call_async(handler, http_state)
                .map(move |result| match result {
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
                                info!("{}", err);
                                Ok(http::Response::builder()
                                    .status(StatusCode::INTERNAL_SERVER_ERROR)
                                    .body("".into())
                                    .unwrap())
                            }
                        }
                    }
                    Err(err) => {
                        info!("{}", err);
                        Ok(http::Response::builder()
                            .status(StatusCode::INTERNAL_SERVER_ERROR)
                            .body("".into())
                            .unwrap())
                    }
                })
                .await
        })
    }
}

// To let the `http_types` module refer to `Body` and `ResponseBody` we register these types in a
// separate function which is called before loading `http_types`
pub fn load_types(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<Body>("std.http.types.Body", &[])?;
    vm.register_type::<ResponseBody>("std.http.types.ResponseBody", &[])?;
    vm.register_type::<Uri>("std.http.types.Uri", &[])?;

    ExternModule::new(
        vm,
        record! {
            // Define the types so that they can be used from gluon
            type std::http::types::Body => Body,
            type std::http::types::ResponseBody => ResponseBody,
            type std::http::types::Uri => Uri,
            type std::http::Method => String,
            type std::http::StatusCode => u16,
            type std::http::Request => Request,
            type std::http::Response => Response,
            type std::http::Headers => Headers,
            type std::http::HttpState => HttpState
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

mod std {
    pub(crate) mod http {
        pub(crate) use crate::std_lib::http as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            listen => primitive!(2, async fn std::http::prim::listen),
            read_chunk => primitive!(1, async fn std::http::prim::read_chunk),
            write_response => primitive!(2, async fn std::http::prim::write_response),
            port => primitive!(1, "std.http.prim.uri.port", |u: &Uri| (u.0).port().map(|p| p.as_u16())),
            uri => uri_binds!(path host query to_string)
        },
    )
}
