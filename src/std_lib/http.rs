use crate::real_std::{fmt, fs, net::SocketAddr, path::PathBuf, pin::Pin, sync::Arc};

use {
    collect_mac::collect,
    futures::{future::BoxFuture, prelude::*},
    http::{
        StatusCode,
        header::{HeaderMap, HeaderName, HeaderValue},
    },
    http_body_util::{BodyExt, Full, StreamBody, combinators::BoxBody},
    hyper::body::{Bytes, Frame, Incoming},
    hyper::service::service_fn,
    hyper_util::{
        rt::{TokioExecutor, TokioIo},
        server::conn::auto::Builder as ServerBuilder,
    },
    tokio::sync::Mutex,
};

use crate::base::types::{ArcType, Type};

use crate::vm::{
    self, ExternModule, Variants,
    api::{
        Collect, Eff, Function, Getable, IO, OpaqueValue, PushAsRef, Pushable, VmType, WithVM,
        generic,
    },
    thread::{ActiveThread, RootedThread, Thread},
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
    let body = body.0.clone();
    async move {
        let mut stream = body.lock().await;
        match stream.as_mut().next().await {
            Some(result) => match result {
                Ok(chunk) => IO::Value(Some(chunk)),
                Err(err) => IO::Exception(err.to_string()),
            },
            None => IO::Value(None),
        }
    }
}

// A http body that is being written
#[derive(Userdata, Trace, VmType, Clone)]
#[gluon(vm_type = "std.http.types.ResponseBody")]
#[gluon(crate_name = "::vm")]
#[gluon_userdata(clone)]
#[gluon_trace(skip)]
pub struct ResponseBody(tokio::sync::mpsc::WeakSender<Bytes>);

impl fmt::Debug for ResponseBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ResponseBody")
    }
}

fn write_response(response: &ResponseBody, bytes: &[u8]) -> impl Future<Output = IO<()>> {
    // Turn `bytes` into `Bytes` which can be sent to the response stream
    let chunk = Bytes::copy_from_slice(bytes);
    let upgrade = response.0.upgrade();
    async move {
        let Some(sender) = upgrade else {
            return IO::Exception("Receiver has been dropped".to_string());
        };
        let permit = match sender.reserve_owned().await {
            Ok(permit) => permit,
            Err(_) => return IO::Exception("Receiver has been dropped".to_string()),
        };
        permit.send(chunk);
        IO::Value(())
    }
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

type RequestBody = Incoming;
type ResponseHttpBody = BoxBody<Bytes, ::std::convert::Infallible>;

async fn listen_(
    settings: Settings,
    thread: RootedThread,
    handler: OpaqueValue<RootedThread, EffectHandler<Response>>,
) -> vm::Result<()> {
    let thread = match thread.new_thread() {
        Ok(thread) => thread,
        Err(err) => return Err(err),
    };

    let addr = SocketAddr::from(([0, 0, 0, 0], settings.port));

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

        let tcp_listener = tokio::net::TcpListener::bind(&addr)
            .map_err(|err| vm::Error::Message(err.to_string()))
            .await?;
        let incoming = tokio_stream::wrappers::TcpListenerStream::new(tcp_listener)
            .err_into()
            .and_then(|stream| {
                acceptor.accept(stream).map_err(|err| {
                    info!("Unable to accept TLS connection: {}", err);
                    Box::new(err) as Box<dyn ::std::error::Error + Send + Sync>
                })
            });

        tokio::pin!(incoming);
        loop {
            let stream = match incoming.next().await {
                Some(Ok(stream)) => stream,
                Some(Err(err)) => {
                    info!("Error accepting TLS connection: {}", err);
                    continue;
                }
                None => break,
            };

            let io = TokioIo::new(stream);
            let listener = listener.clone();
            tokio::spawn(async move {
                let service = service_fn(move |request: hyper::Request<RequestBody>| {
                    let mut listener = listener.clone();
                    async move {
                        Ok::<_, ::std::convert::Infallible>(match request.into_parts() {
                            (parts, body) => match listener
                                .handle(parts.method, parts.uri, body.into_data_stream())
                                .await
                            {
                                Ok(response) => response,
                                Err(err) => {
                                    info!("{}", err);
                                    internal_error_response()
                                }
                            },
                        })
                    }
                });
                if let Err(err) = ServerBuilder::new(TokioExecutor::new())
                    .serve_connection(io, service)
                    .await
                {
                    info!("Server error: {}", err);
                }
            });
        }

        return Ok(());
    }

    let tcp_listener = tokio::net::TcpListener::bind(&addr)
        .map_err(|err| vm::Error::Message(err.to_string()))
        .await?;

    loop {
        let (stream, _) = tcp_listener
            .accept()
            .map_err(|err| vm::Error::Message(err.to_string()))
            .await?;
        let io = TokioIo::new(stream);
        let listener = listener.clone();
        tokio::spawn(async move {
            let service = service_fn(move |request: hyper::Request<RequestBody>| {
                let mut listener = listener.clone();
                async move {
                    Ok::<_, ::std::convert::Infallible>(match request.into_parts() {
                        (parts, body) => match listener
                            .handle(parts.method, parts.uri, body.into_data_stream())
                            .await
                        {
                            Ok(response) => response,
                            Err(err) => {
                                info!("{}", err);
                                internal_error_response()
                            }
                        },
                    })
                }
            });
            if let Err(err) = ServerBuilder::new(TokioExecutor::new())
                .serve_connection(io, service)
                .await
            {
                info!("Server error: {}", err);
            }
        });
    }
}

type ListenFn = fn(OpaqueValue<RootedThread, EffectHandler<Response>>, HttpState) -> IO<Response>;

#[derive(Clone)]
pub struct Handler {
    handle: Function<RootedThread, ListenFn>,
    handler: OpaqueValue<RootedThread, EffectHandler<Response>>,
}

fn internal_error_response() -> hyper::Response<ResponseHttpBody> {
    http::Response::builder()
        .status(StatusCode::INTERNAL_SERVER_ERROR)
        .body(BodyExt::boxed(Full::new(Bytes::new())))
        .unwrap()
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
    ) -> BoxFuture<'static, crate::Result<hyper::Response<ResponseHttpBody>>>
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
        let (response_sender, response_receiver) = tokio::sync::mpsc::channel::<Bytes>(8);
        let response_body = BodyExt::boxed(StreamBody::new(
            tokio_stream::wrappers::ReceiverStream::new(response_receiver)
                .map(|chunk| Ok::<_, ::std::convert::Infallible>(Frame::data(chunk))),
        ));
        let http_state = record_no_decl! {
            request => gluon_request,
            response => ResponseBody(response_sender.downgrade())
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
                                drop(response_sender);

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
                                Ok(internal_error_response())
                            }
                        }
                    }
                    Err(err) => {
                        info!("{}", err);
                        Ok(internal_error_response())
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
