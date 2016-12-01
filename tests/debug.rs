extern crate env_logger;
extern crate gluon;

use std::sync::{Arc, Mutex};

use gluon::base::pos::Line;
use gluon::{Compiler, new_vm};
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
    let lines = Arc::new(Mutex::new(Vec::new()));
    {
        let lines = lines.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            lines.lock().unwrap().push(debug_context.stack_info(0).unwrap().line().unwrap());
            Ok(())
        })));
        context.set_hook_mask(LINE_FLAG);
    }
    Compiler::new().implicit_prelude(false).run_expr::<i32>(&thread, "test", SIMPLE_EXPR).unwrap();

    assert_eq!(*lines.lock().unwrap(),
               vec![1, 3, 4, 3, 1].into_iter().map(Line::from).collect::<Vec<_>>());
}
