extern crate curl;

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::str::from_utf8;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use curl::easy::Easy;

#[test]
fn http() {
    let out_dir_path = PathBuf::from(::std::env::var("OUT_DIR").unwrap());
    let http_path = out_dir_path.parent()
        .and_then(|path| path.parent())
        .and_then(|path| path.parent())
        .expect("http executable")
        .join("examples/http");
    let mut child = Command::new(http_path).spawn().unwrap();

    let start = Instant::now();
    let mut easy = Easy::new();
    easy.url("localhost").unwrap();
    let out = Arc::new(Mutex::new(Vec::new()));
    {
        let out = out.clone();
        easy.write_function(move |data| Ok(out.lock().unwrap().write(data).unwrap()))
            .unwrap();
    }

    let mut response_code = Ok(0);
    while start.elapsed().as_secs() < 7 {
        easy.perform().unwrap();
        response_code = easy.response_code();
        if response_code == Ok(200) {
            break;
        }
    }

    assert_eq!(response_code, Ok(200));
    assert_eq!(from_utf8(&out.lock().unwrap()), Ok("Hello World"));

    child.kill().unwrap();
}
