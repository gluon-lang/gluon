//! This example uses [hyper][] to create a http server which handles requests asynchronously in
//! gluon. To do this we define a few types and functions in Rust with which we register in gluon
//! so that we can communicate with `hyper`. The rest of the implementation is done in gluon,
//! routing the requests and constructing the responses.
//!
//! [hyper]:https://hyper.rs

use std::{env, fs};

use gluon::{
    Thread, ThreadExt, new_vm,
    vm::api::{IO, OwnedFunction},
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

async fn start(thread: &Thread, port: u16) -> Result<(), anyhow::Error> {
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

    use std::str;

    use futures::prelude::*;
    use http_body_util::{BodyExt, Full};
    use hyper::{Request, body::Bytes};
    use hyper_util::{
        client::legacy::{Client, connect::HttpConnector},
        rt::TokioExecutor,
    };

    fn client() -> Client<HttpConnector, Full<Bytes>> {
        Client::builder(TokioExecutor::new()).build_http()
    }

    async fn wait_for_server(port: u16) -> Result<(), anyhow::Error> {
        let mut err = None;
        for _ in 0..40 {
            match client()
                .get(format!("http://localhost:{}", port).parse().unwrap())
                .await
            {
                Ok(response) => {
                    return response
                        .into_body()
                        .collect()
                        .map_ok(|collected| {
                            let body = collected.to_bytes();
                            assert_eq!(str::from_utf8(&body).unwrap(), "Hello World");
                        })
                        .map_err(anyhow::Error::from)
                        .await;
                }
                Err(e) => err = Some(e),
            }
            tokio::time::sleep(std::time::Duration::from_millis(400)).await;
        }
        Err(err.unwrap().into())
    }

    #[tokio::test]
    async fn hello_world() {
        let _ = env_logger::try_init();

        let port = 12234;
        let thread = new_vm();

        let start_server = async move {
            tokio::spawn(async move { start(&thread, port).await.unwrap() });
            wait_for_server(port).await
        };

        start_server.await.unwrap_or_else(|err| panic!("{}", err));
    }

    #[tokio::test]
    async fn echo() {
        let _ = env_logger::try_init();

        let port = 12235;
        let thread = new_vm();
        let start_server = async move {
            tokio::spawn(async move { start(&thread, port).await.unwrap() });
            wait_for_server(port).await
        };

        start_server.await.unwrap_or_else(|err| panic!("{}", err));
        let request = Request::post(format!("http://localhost:{}/echo", port))
            .body(Full::new(Bytes::from_static(b"test")))
            .unwrap();

        client()
            .request(request)
            .err_into::<anyhow::Error>()
            .and_then(|response| {
                response
                    .into_body()
                    .collect()
                    .map_ok(|collected| {
                        let body = collected.to_bytes();
                        assert_eq!(str::from_utf8(&body).unwrap(), "test");
                    })
                    .map_err(anyhow::Error::from)
            })
            .await
            .unwrap_or_else(|err: anyhow::Error| panic!("{}", err));
    }
}
