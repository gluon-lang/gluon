#![cfg(unix)]

extern crate rexpect;

use rexpect::spawn;
use rexpect::session::PtySession;
use rexpect::errors::*;

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

struct REPL {
    session: PtySession,
    prompt: &'static str,
}

impl REPL {
    /// Defines the command, timeout, and prompt settings.
    /// Wraps a rexpect::session::PtySession. expecting the prompt after launch.
    fn new() -> Result<REPL> {
        let command = "../target/debug/gluon -i";
        let timeout: u64 = 10_000;
        let prompt: &'static str = "> ";

        let mut session = spawn(command, Some(timeout))?;
        session.exp_string(prompt)?;

        Ok(REPL { session, prompt })
    }

    /// Ensures certain lines are expected to reduce race conditions.
    /// If no ouput is expected or desired to be tested, pass it an Option::None,
    /// causing rexpect to wait for the next prompt.
    fn test(&mut self, send: &str, expect: Option<&str>) -> Result<()> {
        self.session.send_line(send)?;
        self.session.exp_string(send)?;

        if let Some(string) = expect {
            self.session.exp_string(string)?;
        }

        self.session.exp_string(self.prompt)?;
        Ok(())
    }

    fn quit(&mut self) -> Result<()> {
        let line: &'static str = ":q";
        self.session.send_line(line)?;
        self.session.exp_string(line)?;
        self.session.exp_eof()?;
        Ok(())
    }
}

#[test]
fn prompt() {
    test!({
        let mut repl = REPL::new()?;
        repl.test(repl.prompt, None)?;
    });
}

#[test]
fn exit() {
    test!({
        let mut repl = REPL::new()?;
        repl.quit()?;
    });
}

#[test]
fn hello_world() {
    test!({
        let mut repl = REPL::new()?;

        repl.test("let io = import! std.io", None)?;
        repl.test("io.println \"Hello world\"", Some("Hello world"))?;
    });
}

#[test]
fn expression_types() {
    test!({
        let mut repl = REPL::new()?;

        repl.test(":t 5", Some("Int"))?;
        // repl.test(":t 5 + 5", Some("Int -> Int"))?;
        repl.test(":t \"gluon\"", Some("String"))?;
    });
}

#[test]
fn names() {
    test!({
        let mut repl = REPL::new()?;

        repl.test(
            ":i std.prelude.show",
            Some("std.prelude.show: forall a . [std.prelude.Show a] -> a -> String"),
        )?;
    });
}

#[test]
fn comments() {
    test!({
        let mut repl = REPL::new()?;

        repl.test("1 + 2 // Calls the + function on 1 and 2", Some("3"))?;
        repl.test("1 + 2 /* Calls the + function on 1 and 2 */", Some("3"))?;
    });
}

#[test]
fn if_expressions() {
    test!({
        let mut repl = REPL::new()?;

        repl.test("if True then 1 else 0", Some("1"))?;
        repl.test("if False then 1 else 0", Some("0"))?;
    });
}

#[test]
fn records() {
    test!({
        let mut repl = REPL::new()?;

        repl.test("let record = { pi = 3.14, add1 = (+) 1.0 }", None)?;
        repl.test("record.pi", Some("3.14"))?;

        repl.test("let record_2 = {x = 1 .. record }", None)?;
        repl.test("record_2.x", Some("1"))?;
        repl.test("record_2.pi", Some("3.14"))?;
    });
}

#[test]
fn arrays() {
    test!({
        let mut repl = REPL::new()?;

        repl.test("let array = import! std.array", None)?;
        repl.test("array.len [1, 2, 3]", Some("3"))?;
    });
}
