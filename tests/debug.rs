extern crate env_logger;
extern crate gluon;
#[macro_use]
extern crate collect_mac;

use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;

use gluon::base::pos::Line;
use gluon::{Compiler, Error, new_vm};
use gluon::vm;
use gluon::vm::thread::{ThreadInternal, CALL_FLAG, LINE_FLAG};


const SIMPLE_EXPR: &'static str = r#"
    let f x = x

    let g x = f x
    g 1
    "#;

#[test]
fn function_hook() {
    let _ = env_logger::init();

    let thread = new_vm();
    let functions = Arc::new(Mutex::new(Vec::new()));
    {
        let functions = functions.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            functions.lock()
                .unwrap()
                .push(debug_context.stack_info(0)
                    .unwrap()
                    .function_name()
                    .expect("function_name")
                    .to_string());
            Ok(())
        })));
        context.set_hook_mask(CALL_FLAG);
    }
    Compiler::new().implicit_prelude(false).run_expr::<i32>(&thread, "test", SIMPLE_EXPR).unwrap();

    assert_eq!(*functions.lock().unwrap(),
               vec!["test".to_string(), "g".to_string(), "f".to_string()]);
}

#[test]
fn line_hook() {
    let _ = env_logger::init();

    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, _| Err(vm::Error::Yield))));
        context.set_hook_mask(LINE_FLAG);
    }
    let mut result = Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", SIMPLE_EXPR)
        .map(|_| ());

    let mut lines = Vec::new();
    loop {
        match result {
            Ok(_) => break,
            Err(Error::VM(vm::Error::Yield)) => {
                let context = thread.context();
                let debug_info = context.debug_info();
                lines.push(debug_info.stack_info(0).unwrap().line().unwrap());
            }
            Err(err) => panic!("{}", err),
        }
        result = thread.resume().map_err(From::from);
    }

    assert_eq!(lines,
               vec![1, 3, 4, 3, 1].into_iter().map(Line::from).collect::<Vec<_>>());
}

#[test]
fn implicit_prelude_lines_not_counted() {
    let _ = env_logger::init();

    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_info| {
            if debug_info.stack_info(0).unwrap().source_name() == "test" {
                Err(vm::Error::Yield)
            } else {
                Ok(())
            }
        })));
        context.set_hook_mask(LINE_FLAG);
    }
    let mut result = Compiler::new()
        .run_expr::<i32>(&thread, "test", "1")
        .map(|_| ());

    let mut lines = Vec::new();
    loop {
        match result {
            Ok(_) => break,
            Err(Error::VM(vm::Error::Yield)) => {
                let context = thread.context();
                let debug_info = context.debug_info();
                let stack_info = debug_info.stack_info(0).unwrap();
                lines.push(stack_info.line().unwrap());
            }
            Err(err) => panic!("{}", err),
        }
        result = thread.resume().map_err(From::from);
    }

    assert_eq!(lines, vec![Line::from(0)]);
}

#[test]
fn read_variables() {
    let _ = env_logger::init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(BTreeMap::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            result.lock().unwrap().insert(stack_info.line().unwrap().to_usize(),
                                          stack_info.locals()
                                              .map(|s| s.to_string())
                                              .collect::<Vec<_>>());
            Ok(())
        })));
        context.set_hook_mask(LINE_FLAG);
    }
    let expr = r#"
    let x = 1
    let y =
        let y2 = ""
        ()

    ()
    let z = { x }
    1
    "#;
    Compiler::new().implicit_prelude(false).run_expr::<i32>(&thread, "test", expr).unwrap();

    let map = result.lock().unwrap();
    assert_eq!(*map,
               collect![(1, vec![]),
                        (3, vec!["x".to_string()]),
                        (4, vec!["x".to_string(), "y2".to_string()]),
                        (6, vec!["x".to_string(), "y".to_string()]),
                        (7, vec!["x".to_string(), "y".to_string()]),
                        (8, vec!["x".to_string(), "y".to_string(), "z".to_string()])]);
}

#[test]
fn source_name() {
    let _ = env_logger::init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(String::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            *result.lock().unwrap() = stack_info.source_name().to_string();
            Ok(())
        })));
        context.set_hook_mask(LINE_FLAG);
    }
    let expr = r#"
    let x = 1
    let y =
        let y2 = ""
        ()

    ()
    let z = { x }
    1
    "#;
    Compiler::new().implicit_prelude(false).run_expr::<i32>(&thread, "test", expr).unwrap();

    let name = result.lock().unwrap();
    assert_eq!(*name, "test");
}
