#[macro_use]
extern crate collect_mac;
extern crate env_logger;
extern crate futures;
extern crate gluon;

use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;

use futures::{Async, Future};

use gluon::base::pos::Line;
use gluon::base::types::{ArcType, Type};
use gluon::{new_vm, Compiler};
use gluon::vm::compiler::UpvarInfo;
use gluon::vm::thread::{HookFlags, ThreadInternal};

const SIMPLE_EXPR: &'static str = r#"
    let f x = x

    let g x = f x
    g 1
    "#;

#[test]
fn function_hook() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let functions = Arc::new(Mutex::new(Vec::new()));
    {
        let functions = functions.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            functions.lock().unwrap().push(
                debug_context
                    .stack_info(0)
                    .unwrap()
                    .function_name()
                    .expect("function_name")
                    .to_string(),
            );
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::CALL_FLAG);
    }
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", SIMPLE_EXPR)
        .unwrap();

    assert_eq!(
        *functions.lock().unwrap(),
        vec!["test".to_string(), "g".to_string(), "f".to_string()]
    );
}

fn run_line_hook_test(source: &str) -> Vec<Line> {
    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, _| Ok(Async::NotReady))));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let mut execute = Compiler::new()
        .implicit_prelude(false)
        .run_expr_async::<i32>(&thread, "test", source)
        .map(|_| ());
    let mut result = Ok(Async::NotReady);

    let mut lines = Vec::new();
    loop {
        match result {
            Ok(Async::Ready(())) => break,
            Ok(Async::NotReady) => {
                let context = thread.context();
                let debug_info = context.debug_info();
                lines.push(
                    debug_info
                        .stack_info(0)
                        .expect("stack info")
                        .line()
                        .expect("expected line"),
                );
            }
            Err(err) => panic!("{}", err),
        }
        result = execute.poll();
    }
    lines
}

#[test]
fn line_hook() {
    let _ = env_logger::try_init();

    let lines = run_line_hook_test(SIMPLE_EXPR);
    assert_eq!(
        lines,
        vec![1, 3, 4, 3, 1]
            .into_iter()
            .map(Line::from)
            .collect::<Vec<_>>()
    );
}

#[test]
fn line_hook_recursive_functions() {
    let _ = env_logger::try_init();

    let expr = r#"
let f x = x
and g y = f
1
    "#;

    let lines = run_line_hook_test(expr);
    assert_eq!(
        lines,
        vec![1, 2, 3]
            .into_iter()
            .map(Line::from)
            .collect::<Vec<_>>()
    );
}

#[test]
fn line_hook_after_call() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, _| Ok(Async::NotReady))));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }

    let expr = r#"
        let id x = x
        id 0
        1
    "#;
    let mut execute = Compiler::new()
        .implicit_prelude(false)
        .run_expr_async::<i32>(&thread, "test", expr)
        .map(|_| ());
    let mut result = Ok(Async::NotReady);

    let mut lines = Vec::new();
    loop {
        match result {
            Ok(Async::Ready(())) => break,
            Ok(Async::NotReady) => {
                let context = thread.context();
                let debug_info = context.debug_info();
                lines.push(debug_info.stack_info(0).unwrap().line().unwrap());
            }
            Err(err) => panic!("{}", err),
        }
        result = execute.poll();
    }

    assert_eq!(
        lines,
        vec![1, 2, 1, 3]
            .into_iter()
            .map(Line::from)
            .collect::<Vec<_>>()
    );
}

#[test]
fn implicit_prelude_lines_not_counted() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_info| {
            if debug_info.stack_info(0).unwrap().source_name() == "test" {
                Ok(Async::NotReady)
            } else {
                Ok(Async::Ready(()))
            }
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let mut execute = Compiler::new()
        .run_expr_async::<i32>(&thread, "test", "1")
        .map(|_| ());
    let mut result = Ok(Async::NotReady);

    let mut lines = Vec::new();
    loop {
        match result {
            Ok(Async::Ready(())) => break,
            Ok(Async::NotReady) => {
                let context = thread.context();
                let debug_info = context.debug_info();
                let stack_info = debug_info.stack_info(0).unwrap();
                lines.push(stack_info.line().unwrap());
            }
            Err(err) => panic!("{}", err),
        }
        result = execute.poll();
    }

    assert_eq!(lines, vec![Line::from(0)]);
}

#[test]
fn read_variables() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(BTreeMap::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            result.lock().unwrap().insert(
                stack_info.line().unwrap().to_usize(),
                stack_info
                    .locals()
                    .map(|local| (local.name.declared_name().to_string(), local.typ.clone()))
                    .collect::<Vec<_>>(),
            );
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let expr = r#"
    let x = 1
    let y =
        let y2 = ""
        ()

    ()
    let z = 1.0
    1
    "#;
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", expr)
        .unwrap();

    let map = result.lock().unwrap();
    assert_eq!(
        *map,
        collect![
            (1, vec![]),
            (3, vec![("x".to_string(), Type::int())]),
            (
                4,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y2".to_string(), Type::string()),
                ]
            ),
            (
                6,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                ]
            ),
            (
                7,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                ]
            ),
            (
                8,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                    ("z".to_string(), Type::float()),
                ]
            ),
        ]
    );
}

#[test]
fn argument_types() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(Vec::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            result.lock().unwrap().push((
                stack_info.line().unwrap().to_usize(),
                stack_info
                    .locals()
                    .map(|local| (local.name.declared_name().to_string(), local.typ.clone()))
                    .collect::<Vec<_>>(),
            ));
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let expr = r#"
    let int_function x: Int -> Int = x
    let g = \y -> int_function y
    let f z = g z
    f 1
    "#;
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", expr)
        .unwrap();

    let int_function: ArcType = Type::function(vec![Type::int()], Type::int());

    let map = result.lock().unwrap();
    assert_eq!(
        *map,
        vec![
            (1, vec![]),
            (2, vec![("int_function".to_string(), int_function.clone())]),
            (
                3,
                vec![
                    ("int_function".to_string(), int_function.clone()),
                    ("g".to_string(), int_function.clone()),
                ],
            ),
            (
                4,
                vec![
                    ("int_function".to_string(), int_function.clone()),
                    ("g".to_string(), int_function.clone()),
                    ("f".to_string(), int_function.clone()),
                ],
            ),
            (3, vec![("z".to_string(), Type::int())]),
            (2, vec![("y".to_string(), Type::int())]),
            (1, vec![("x".to_string(), Type::int())]),
        ]
    );
}

#[test]
fn source_name() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(String::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            *result.lock().unwrap() = stack_info.source_name().to_string();
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
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
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", expr)
        .unwrap();

    let name = result.lock().unwrap();
    assert_eq!(*name, "test");
}

#[test]
fn upvars() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let result = Arc::new(Mutex::new(Vec::new()));
    {
        let result = result.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_info| {
            let stack_info = debug_info.stack_info(0).unwrap();
            if stack_info.source_name() == "test" {
                result.lock().unwrap().push(stack_info.upvars().to_owned());
            }
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::CALL_FLAG);
    }
    let expr = r#"
    let x = 1
    let y = 2
    let f z =
        let g w = x
        g x #Int+ y #Int+ z
    f 3
    "#;
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<i32>(&thread, "test", expr)
        .unwrap();

    assert_eq!(
        *result.lock().unwrap(),
        vec![
            vec![],
            vec![
                UpvarInfo {
                    name: "x".to_string(),
                    typ: Type::int(),
                },
                UpvarInfo {
                    name: "y".to_string(),
                    typ: Type::int(),
                },
            ],
            vec![
                UpvarInfo {
                    name: "x".to_string(),
                    typ: Type::int(),
                },
            ],
        ]
    );
}

#[test]
fn implicit_prelude_variable_names() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let functions = Arc::new(Mutex::new(Vec::<ArcType>::new()));
    {
        let functions = functions.clone();
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, debug_context| {
            let stack_info = debug_context.stack_info(0).unwrap();
            functions.lock().unwrap().extend(
                stack_info
                    .locals()
                    .filter(|local| local.name.declared_name() == "__implicit_prelude")
                    .map(|local| local.typ.clone()),
            );
            Ok(Async::Ready(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    Compiler::new()
        .run_expr::<i32>(&thread, "test", "\n1")
        .unwrap();
    let f = functions.lock().unwrap();
    match *f[0] {
        Type::Record(ref row) => {
            assert!(
                row.row_iter()
                    .any(|field| field.name.declared_name() == "+")
            );
        }
        _ => panic!(),
    }
}
