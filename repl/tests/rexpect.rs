#![cfg(unix)]

extern crate rexpect;

use rexpect::spawn;
use rexpect::errors::*;

static COMMAND: &str = "../target/debug/gluon -i";
static TIMEOUT: u64 = 10_000;
static PROMPT: &str = "> ";

macro_rules! test {
    ($b: block) => {
        if ::std::env::var("GLUON_PATH").is_err() {
            ::std::env::set_var("GLUON_PATH", "..");
        }

        || -> Result<()> {
            $b
            Ok(())
        }().unwrap_or_else(|err| panic!("{}", err));
    };
}

#[test]
fn prompt() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;
    });
}

#[test]
fn exit() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line(":q")?;
        repl.exp_eof()?;
    });
}

#[test]
fn hello_world() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line("let io = import! std.io")?;

        repl.exp_regex("\\{[^}]+\\}")?;

        repl.send_line("io.println \"Hello world\"")?;
        repl.exp_string("Hello world")?;
    });
}

#[test]
fn expression_types() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line(":t 5")?;
        repl.exp_string("Int")?;

        repl.send_line(":t 5 + 5")?;
        repl.exp_string("Int -> Int")?;

        repl.send_line(":t \"gluon\"")?;
        repl.exp_string("String")?;
    });
}

#[test]
fn names() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line(":i std.prelude.show")?;
        repl.exp_string("std.prelude.show: forall a . [std.prelude.Show a] -> a -> String")?;
    });
}

#[test]
fn comments() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line("1 + 2 // Calls the + function on 1 and 2")?;
        repl.exp_string("3")?;

        repl.send_line("1 + 2 /* Calls the + function on 1 and 2 */")?;
        repl.exp_string("3")?;
    });
}

#[test]
fn if_expressions() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line("if True then 1 else 0")?;
        repl.exp_string("1")?;

        repl.send_line("if False then 1 else 0")?;
        repl.exp_string("0")?;
    });
}

#[test]
fn records() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line("let record = { pi = 3.14, add1 = (+) 1.0 }")?;

        repl.send_line("record.pi")?;
        repl.exp_string("3.14")?;

        repl.send_line("let record_2 = {x = 1 .. record }")?;

        repl.send_line("record_2.x")?;
        repl.exp_string("1")?;

        repl.send_line("record_2.pi")?;
        repl.exp_string("3.14")?;
    });
}

#[test]
fn arrays() {
    test!({
        let mut repl = spawn(COMMAND, Some(TIMEOUT))?;
        repl.exp_string(PROMPT)?;

        repl.send_line("let array = import! std.array")?;

        repl.send_line("array.len [1, 2, 3]")?;
        repl.exp_string("3")?;
    });
}
