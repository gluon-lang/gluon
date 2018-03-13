#[macro_use]
extern crate pretty_assertions;

extern crate rexpect;

use rexpect::spawn;

use std::env;
use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};

#[test]
fn fmt_repl() {
    let source = "src/repl.glu";

    let mut before = String::new();
    File::open(source)
        .unwrap()
        .read_to_string(&mut before)
        .unwrap();

    let status = Command::new("../target/debug/gluon")
        .args(&["fmt", source])
        .spawn()
        .expect("Could not find gluon executable")
        .wait()
        .unwrap();
    assert!(status.success());

    let mut after = String::new();
    File::open(source)
        .unwrap()
        .read_to_string(&mut after)
        .unwrap();

    assert_eq!(before, after);
}

#[test]
fn issue_365_run_io_from_command_line() {
    if ::std::env::var("GLUON_PATH").is_err() {
        ::std::env::set_var("GLUON_PATH", "..");
    }

    let path = env::args().next().unwrap();
    let gluon_path = Path::new(&path[..])
        .parent()
        .and_then(|p| p.parent())
        .expect("folder")
        .join("gluon");
    let output = Command::new(&*gluon_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .arg("tests/print.glu")
        .output()
        .unwrap_or_else(|err| panic!("{}\nWhen opening `{}`", err, gluon_path.display()));

    let stderr = String::from_utf8_lossy(&output.stderr);
    if stderr != "" {
        panic!("{}", stderr);
    }
    assert_eq!(String::from_utf8_lossy(&output.stdout), "123\n");
}


static COMMAND: &str = "../target/debug/gluon -i";
static TIMEOUT: u64 = 10_000;
static PROMPT: &str = "> ";

macro_rules! test {
    ($e: expr) => { $e.unwrap_or_else(|err| panic!("{}", err)) }
}

#[test]
fn prompt() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));
}

#[test]
fn exit() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line(":q"));
    test!(repl.exp_eof());
}


#[test]
#[ignore] // TODO fix intermittent test failure
fn hello_world() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line("let io = import! std.io"));

    test!(repl.send_line("io.println \"Hello world\""));
    test!(repl.exp_string("Hello world"));
}

#[test]
fn expression_types() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line(":t 5"));
    test!(repl.exp_string("Int"));

    test!(repl.send_line(":t 5 + 5"));
    test!(repl.exp_string("Int -> Int"));

    test!(repl.send_line(":t \"gluon\""));
    test!(repl.exp_string("String"));
}

#[test]
fn names() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line(":i std.prelude.show"));
    test!(repl.exp_string("std.prelude.show: forall a . [std.prelude.Show a] -> a -> String"));
}

#[test]
fn comments() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line("1 + 2 // Calls the + function on 1 and 2"));
    test!(repl.exp_string("3"));

    test!(repl.send_line("1 + 2 /* Calls the + function on 1 and 2 */"));
    test!(repl.exp_string("3"));
}

#[test]
fn if_expressions() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line("if True then 1 else 0"));
    test!(repl.exp_string("1"));

    test!(repl.send_line("if False then 1 else 0"));
    test!(repl.exp_string("0"));
}

#[test]
fn records() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line("let record = { pi = 3.14, add1 = (+) 1.0 }"));

    test!(repl.send_line("record.pi"));
    test!(repl.exp_string("3.14"));

    test!(repl.send_line("let record_2 = {x = 1 .. record }"));

    test!(repl.send_line("record_2.x"));
    test!(repl.exp_string("1"));

    test!(repl.send_line("record_2.pi"));
    test!(repl.exp_string("3.14"));
}

#[test]
fn arrays() {
    let mut repl = test!(spawn(COMMAND, Some(TIMEOUT)));
    test!(repl.exp_string(PROMPT));

    test!(repl.send_line("let array = import! std.array"));

    test!(repl.send_line("array.len [1, 2, 3]"));
    test!(repl.exp_string("3"));
}


