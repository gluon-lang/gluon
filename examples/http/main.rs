//! This example uses [hyper][] to create a http server which handles requests asynchronously in
//! gluon. To do this we define a few types and functions in Rust with which we register in gluon
//! so that we can communicate with `hyper`. The rest of the implementation is done in gluon,
//! routing the requests and constructing the responses.
//!
//! [hyper]:https://hyper.rs

extern crate gluon;

extern crate env_logger;
#[allow(unused_imports)]
#[macro_use]
extern crate log;
extern crate futures;
extern crate tokio;

use std::env;
use std::error::Error as StdError;
use std::fs::File;
use std::io::Read;

use futures::{future, Future};

use gluon::{
    new_vm,
    vm::{
        api::{OwnedFunction, IO},
        thread::Thread,
    },
    Compiler,
};

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
            ).from_err()
            .and_then(move |(mut listen, _)| listen.call_async(port).from_err().map(|_| ()))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate hyper;
    extern crate tokio_retry;

    use std::str;

    use self::hyper::Client;
    use futures::Stream;
    use tokio::runtime::Runtime;

    #[test]
    fn hello_world() {
        let mut runtime = Runtime::new().unwrap();

        let port = 12235;
        let thread = new_vm();

        runtime.spawn(future::lazy(move || {
            start(&thread, port).map_err(|err| error!("{}", err))
        }));

        let future =
            move || Client::new().get(format!("http://localhost:{}", port).parse().unwrap());

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(40);

        runtime
            .block_on(
                tokio_retry::Retry::spawn(retry_strategy, future)
                    .map_err(|err| panic!("{}", err))
                    .and_then(|response| {
                        response.into_body().concat2().map(|body| {
                            assert_eq!(str::from_utf8(&body).unwrap(), "Hello World");
                        })
                    }),
            ).unwrap();
    }

    #[test]
    fn echo() {
        let mut runtime = Runtime::new().unwrap();

        let port = 12234;
        let thread = new_vm();
        runtime.spawn(future::lazy(move || {
            start(&thread, port).map_err(|err| error!("{}", err))
        }));

        let future = move || {
            let request = hyper::Request::post(format!("http://localhost:{}/echo", port))
                .body(hyper::Body::from("test"))
                .unwrap();

            Client::new().request(request)
        };

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(40);

        runtime
            .block_on(
                tokio_retry::Retry::spawn(retry_strategy, future)
                    .map_err(|err| panic!("{}", err))
                    .and_then(|response| {
                        response.into_body().concat2().map(|body| {
                            assert_eq!(str::from_utf8(&body).unwrap(), "test");
                        })
                    }),
            ).unwrap();
    }
}
