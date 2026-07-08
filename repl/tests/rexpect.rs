#![cfg(unix)]

extern crate rexpect;

use std::process::Command;

use rexpect::session::{Options, PtySession, spawn_with_options};

use anyhow::{Context as _, Result};

struct REPL {
    session: PtySession,
    prompt: &'static str,
}

impl REPL {
    fn new() -> REPL {
        let repl = REPL::new_(false).unwrap_or_else(|err| panic!("{}", err));
        repl
    }

    fn new_completion() -> REPL {
        let repl = REPL::new_(true).unwrap_or_else(|err| panic!("{}", err));
        repl
    }

    /// Defines the command, timeout, and prompt settings.
    /// Wraps a rexpect::session::PtySession. expecting the prompt after launch.
    fn new_(auto_complete: bool) -> Result<REPL> {
        let _ = env_logger::try_init();

        let timeout: u64 = 5_000;
        let prompt: &'static str = "REXPECT> ";

        let mut command = Command::new("../target/debug/gluon");
        command
            .args(&["-i", "--color", "never", "--prompt", prompt])
            .env("GLUON_PATH", "..");

        if !auto_complete {
            command.arg("--no-auto-complete");
        }
        let mut session = spawn_with_options(
            command,
            Options::new()
                .timeout_ms(Some(timeout))
                .strip_ansi_escape_codes(true),
        )?;

        session.exp_string(prompt)?;

        Ok(REPL { session, prompt })
    }

    #[track_caller]
    fn test(&mut self, send: &str, expect: Option<&str>) {
        self.test_(send, expect)
            .unwrap_or_else(|err| panic!("{:#}", err));
    }

    /// Ensures certain lines are expected to reduce race conditions.
    /// If no ouput is expected or desired to be tested, pass it an Option::None,
    /// causing rexpect to wait for the next prompt.
    #[track_caller]
    fn test_(&mut self, send: &str, expect: Option<&str>) -> Result<()> {
        self.session.send_line(send)?;
        self.session.exp_string(send).context("Send string")?;

        if let Some(string) = expect {
            self.session.exp_string(string).context("Expect string")?;
        }

        self.session
            .exp_string(self.prompt)
            .context("Expect prompt")?;
        Ok(())
    }

    #[track_caller]
    fn test_completion(&mut self, prefix: &str, expect: &str) {
        self.session.send(prefix).unwrap();
        self.session.send("\t").unwrap();
        self.session.flush().unwrap();
        self.session.exp_string(expect).unwrap();
    }

    fn quit(&mut self) {
        self.quit_().unwrap_or_else(|err| panic!("{:#}", err));
    }

    fn quit_(&mut self) -> Result<()> {
        let line: &'static str = ":q";
        self.session.send_line(line)?;
        self.session.exp_string(line)?;
        self.session.exp_eof()?;
        Ok(())
    }
}

#[test]
fn prompt() {
    let _repl = REPL::new();
}

#[test]
#[ignore]
fn quit() {
    let mut repl = REPL::new();
    repl.quit();
}

#[test]
fn hello_world() {
    let mut repl = REPL::new();

    repl.test("let io = import! std.io", None);
    repl.test("io.println \"Hello world\"", Some("Hello world"));
}

#[test]
fn expression_types() {
    let mut repl = REPL::new();

    repl.test(":t 5", Some("Int"));
    repl.test(":t 5 + 5", Some("Int"));
    repl.test(":t \"gluon\"", Some("String"));
}

#[test]
fn names() {
    let mut repl = REPL::new();

    repl.test(
        ":i std.prelude.show",
        Some("std.prelude.show: forall a . [std.show.Show a] -> a -> String"),
    );
}

#[test]
fn comments() {
    let mut repl = REPL::new();

    repl.test("1 + 2 // Calls the + function on 1 and 2", Some("3"));
    repl.test("1 + 2 /* Calls the + function on 1 and 2 */", Some("3"));
}

#[test]
fn if_expressions() {
    let mut repl = REPL::new();

    repl.test("if True then 1 else 0", Some("1"));
    repl.test("if False then 1 else 0", Some("0"));
}

#[test]
fn records() {
    let mut repl = REPL::new();

    repl.test("let record = { pi = 3.14, add1 = (+) 1.0 }", None);
    repl.test("record.pi", Some("3.14"));

    repl.test("let record_2 = {x = 1 .. record }", None);
    repl.test("record_2.x", Some("1"));
    repl.test("record_2.pi", Some("3.14"));
}

#[test]
fn arrays() {
    let mut repl = REPL::new();

    repl.test("let array = import! std.array", None);
    repl.test("array.len [1, 2, 3]", Some("3"));
}

#[test]
fn comment() {
    let mut repl = REPL::new();

    repl.test("// test", None);
}

#[test]
fn error_reports_correct_line() {
    let mut repl = REPL::new();

    repl.test("let { x } = {}", Some("let { x } = {}"));
}

#[test]
fn import() {
    let mut repl = REPL::new();

    repl.test("let { assert } = import! std.test", None);
}

#[test]
fn assert() {
    let mut repl = REPL::new();

    repl.test("let { assert } = import! std.test", None);
    repl.test("assert False", None);
}

#[test]
fn completion() {
    let mut repl = REPL::new_completion();

    repl.test("let abc = 1", None);
    repl.test_completion("a", "abc");
    repl.session.send_line("let abc2 = 1").unwrap();
    repl.session.send_line("let acc = 1").unwrap();
    repl.test_completion("ab", "abc");
    repl.test_completion("", "abc2");
}
