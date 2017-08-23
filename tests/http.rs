extern crate curl;

use std::cmp;
use std::io::Write;
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use curl::easy::Easy;
use curl::Error;

fn test_server(
    easy: &mut Easy,
    port: &str,
    path: &str,
    mut message: &'static [u8],
) -> Result<String, Option<Error>> {
    let http_path = "./target/debug/examples/http";
    let mut child = Command::new(http_path).arg(port).spawn().unwrap();

    let start = Instant::now();
    easy.url(&format!("localhost:{}{}", port, path)).unwrap();
    let out = Arc::new(Mutex::new(Vec::new()));
    easy.read_function(move |buffer| {
        let len = cmp::min(buffer.len(), message.len());
        buffer[..len].copy_from_slice(&message[..len]);
        message = &message[len..];
        Ok(len)
    })?;
    {
        let out = out.clone();
        easy.write_function(move |data| Ok(out.lock().unwrap().write(data).unwrap()))
            .unwrap();
    }

    let mut result = None;
    while start.elapsed().as_secs() < 7 {
        result = Some(easy.perform());
        if let Some(Ok(())) = result {
            break;
        }
    }

    child.kill().unwrap();
    match result {
        None => Err(None),
        Some(Err(err)) => return Err(Some(err)),
        Some(Ok(())) => Ok(String::from_utf8(out.lock().unwrap().to_owned()).unwrap()),
    }
}

#[test]
fn http() {
    let mut easy = Easy::new();
    let result = test_server(&mut easy, "2345", "", b"");

    assert_eq!(easy.response_code(), Ok(200));
    assert_eq!(result, Ok("Hello World".to_string()));
}

#[test]
fn echo() {
    let mut easy = Easy::new();
    easy.post(true).unwrap();
    let content = b"test message";
    easy.post_field_size(content.len() as u64).unwrap();
    let result = test_server(&mut easy, "2346", "/echo", content);

    assert_eq!(easy.response_code(), Ok(200));
    assert_eq!(result, Ok("test message".to_string()));
}
