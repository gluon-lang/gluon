#[macro_use]
extern crate collect_mac;
#[macro_use]
extern crate pretty_assertions;

use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

use futures::{prelude::*, task::Poll};

use gluon::{
    base::{
        pos::Line,
        types::{ArcType, Type, TypeExt},
    },
    vm::{
        compiler::UpvarInfo,
        thread::{HookFlags, ThreadInternal},
    },
    RootedThread, ThreadExt,
};

fn new_vm() -> RootedThread {
    let thread = gluon::new_vm();

    thread.get_database_mut().set_optimize(false);
    thread
}

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
            Poll::Ready(Ok(()))
        })));
        context.set_hook_mask(HookFlags::CALL_FLAG);
    }

    thread.get_database_mut().implicit_prelude(false);

    thread.run_expr::<i32>("test", SIMPLE_EXPR).unwrap();

    assert_eq!(
        *functions.lock().unwrap(),
        vec!["test".to_string(), "g".to_string(), "f".to_string()]
    );
}

fn run_line_hook_test(source: &str) -> Vec<Line> {
    let thread = new_vm();
    {
        let mut context = thread.context();
        context.set_hook(Some(Box::new(move |_, _| Poll::Pending)));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }

    thread.get_database_mut().implicit_prelude(false);

    let execute = thread.run_expr_async::<i32>("test", source).map_ok(|_| ());
    futures::pin_mut!(execute);
    let mut result = Poll::Pending;

    let mut lines = Vec::new();
    futures::executor::block_on(future::lazy(|cx| loop {
        match &result {
            Poll::Ready(Ok(())) => break,
            Poll::Pending => {
                let context = thread.context();
                let debug_info = context.debug_info();
                lines.extend(debug_info.stack_info(0).expect("stack info").line());
            }
            Poll::Ready(Err(err)) => panic!("{}", err),
        }
        result = execute.poll_unpin(cx);
    }));
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
rec
let f x = x
let g y = f
1
    "#;

    let lines = run_line_hook_test(expr);
    assert_eq!(
        lines,
        vec![1, 2, 3, 4]
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
        context.set_hook(Some(Box::new(move |_, _| Poll::Pending)));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }

    let expr = r#"
        let id x = x
        let _ = id 0
        1
    "#;

    thread.get_database_mut().implicit_prelude(false);

    let execute = thread.run_expr_async::<i32>("test", expr).map_ok(|_| ());
    futures::pin_mut!(execute);
    let mut result = Poll::Pending;

    let mut lines = Vec::new();
    futures::executor::block_on(future::lazy(|cx| loop {
        match &result {
            Poll::Ready(Ok(())) => break,
            Poll::Pending => {
                let context = thread.context();
                let debug_info = context.debug_info();
                lines.extend(debug_info.stack_info(0).and_then(|s| s.line()));
            }
            Poll::Ready(Err(err)) => panic!("{}", err),
        }
        result = execute.poll_unpin(cx);
    }));

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
            eprintln!("{}", debug_info.stack_info(0).unwrap().source_name());
            if debug_info.stack_info(0).unwrap().source_name() == "test" {
                Poll::Pending
            } else {
                Poll::Ready(Ok(()))
            }
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let execute = thread.run_expr_async::<i32>("test", "1").map_ok(|_| ());
    futures::pin_mut!(execute);
    let mut result = Poll::Pending;

    let mut lines = Vec::new();
    futures::executor::block_on(future::lazy(|cx| loop {
        match &result {
            Poll::Ready(Ok(())) => break,
            Poll::Pending => {
                let context = thread.context();
                let debug_info = context.debug_info();
                let stack_info = debug_info.stack_info(0).unwrap();
                lines.extend(stack_info.line());
            }
            Poll::Ready(Err(err)) => panic!("{}", err),
        }
        result = execute.poll_unpin(cx);
    }));

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
            Poll::Ready(Ok(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let expr = r#"
    let x = 1
    let y =
        let y2 = ""
        ()

    let _ = ()
    let z = 1.0
    1
    "#;

    thread.get_database_mut().implicit_prelude(false);

    thread
        .run_expr::<i32>("test", expr)
        .unwrap_or_else(|err| panic!("{}", err));

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
                ],
            ),
            (
                6,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                ],
            ),
            (
                7,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                    ("_".to_string(), Type::unit()),
                ],
            ),
            (
                8,
                vec![
                    ("x".to_string(), Type::int()),
                    ("y".to_string(), Type::unit()),
                    ("_".to_string(), Type::unit()),
                    ("z".to_string(), Type::float()),
                ],
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
            Poll::Ready(Ok(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let expr = r#"
    let int_function x: Int -> Int = x
    let g = \y -> int_function y
    let f z = g z
    f 1
    "#;

    thread.get_database_mut().implicit_prelude(false);

    thread.run_expr::<i32>("test", expr).unwrap();

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
            Poll::Ready(Ok(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    let expr = r#"
    let x = 1
    let y =
        let y2 = ""
        ()

    let _ = ()
    let z = { x }
    1
    "#;

    thread.get_database_mut().implicit_prelude(false);

    thread.run_expr::<i32>("test", expr).unwrap();

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
            Poll::Ready(Ok(()))
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

    thread.get_database_mut().implicit_prelude(false);

    thread.run_expr::<i32>("test", expr).unwrap();

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
            vec![UpvarInfo {
                name: "x".to_string(),
                typ: Type::int(),
            }],
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
            eprintln!("1123");
            let stack_info = debug_context.stack_info(0).unwrap();
            functions.lock().unwrap().extend(
                stack_info
                    .locals()
                    .filter(|local| local.name.declared_name() == "__implicit_prelude")
                    .map(|local| local.typ.clone()),
            );
            Poll::Ready(Ok(()))
        })));
        context.set_hook_mask(HookFlags::LINE_FLAG);
    }
    thread.run_expr::<i32>("test", "\n1").unwrap();
    let f = functions.lock().unwrap();
    match *f[0] {
        Type::Record(ref row) => {
            assert!(row
                .row_iter()
                .any(|field| field.name.declared_name() == "+"));
        }
        _ => panic!("{:#?}", f[0]),
    }
}
