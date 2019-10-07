//! This example uses [hyper][] to create a http server which handles requests asynchronously in
//! gluon. To do this we define a few types and functions in Rust with which we register in gluon
//! so that we can communicate with `hyper`. The rest of the implementation is done in gluon,
//! routing the requests and constructing the responses.
//!
//! [hyper]:https://hyper.rs

use std::{env, fs};

use gluon::{
    new_vm,
    vm::api::{OwnedFunction, IO},
    Thread, ThreadExt,
};

#[tokio::main]
async fn main() {
    env_logger::init();

    let port = env::args()
        .nth(1)
        .map(|port| port.parse::<u16>().expect("port"))
        .unwrap_or(80);

    let thread = new_vm();
    if let Err(err) = start(&thread, port).await {
        panic!("{}", err)
    }
}

async fn start(thread: &Thread, port: u16) -> Result<(), failure::Error> {
    let thread = thread.root_thread();
    // Last we run our `http_server.glu` module which returns a function which starts listening
    // on the port we passed from the command line
    let expr = fs::read_to_string("examples/http/server.glu")?;
    let (mut listen, _) = thread
        .run_expr_async::<OwnedFunction<fn(u16) -> IO<()>>>("examples/http/server.glu", &expr)
        .await?;
    listen.call_async(port).await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    extern crate hyper;
    extern crate tokio_retry;

    use std::str;

    use self::hyper::Client;
    use tokio::runtime::Runtime;

    fn wait_for_server(port: u16) -> impl Future<Item = (), Error = failure::Error> {
        let future =
            move || Client::new().get(format!("http://localhost:{}", port).parse().unwrap());

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(40);

        tokio_retry::Retry::spawn(retry_strategy, future)
            .from_err::<failure::Error>()
            .and_then(|response| {
                response
                    .into_body()
                    .concat2()
                    .map(|body| {
                        assert_eq!(str::from_utf8(&body).unwrap(), "Hello World");
                    })
                    .from_err::<failure::Error>()
            })
    }

    #[test]
    fn hello_world() {
        let _ = env_logger::try_init();

        let mut runtime = Runtime::new().unwrap();

        let port = 12234;
        let thread = new_vm();

        let start_server = future::lazy(move || start(&thread, port));

        let _ = runtime
            .block_on(
                start_server
                    .select(wait_for_server(port))
                    .map_err(|(err, _)| err),
            )
            .unwrap_or_else(|err| panic!("{}", err));
    }

    #[test]
    fn echo() {
        let _ = env_logger::try_init();

        let mut runtime = Runtime::new().unwrap();

        let port = 12235;
        let thread = new_vm();
        let start_server = future::lazy(move || start(&thread, port));

        let future = move || {
            let request = hyper::Request::post(format!("http://localhost:{}/echo", port))
                .body(hyper::Body::from("test"))
                .unwrap();

            Client::new().request(request)
        };

        let retry_strategy = tokio_retry::strategy::FixedInterval::from_millis(400).take(40);

        let _ = runtime
            .block_on(
                start_server
                    .select(
                        tokio_retry::Retry::spawn(retry_strategy, future)
                            .from_err::<failure::Error>()
                            .and_then(|response| {
                                response
                                    .into_body()
                                    .concat2()
                                    .map(|body| {
                                        assert_eq!(str::from_utf8(&body).unwrap(), "test");
                                    })
                                    .from_err::<failure::Error>()
                            }),
                    )
                    .map_err(|(err, _)| err),
            )
            .unwrap_or_else(|err| panic!("{}", err));
    }
}
