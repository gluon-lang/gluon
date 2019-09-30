# Embedding API

The API with which the host language interacts with Gluon is very important part of the library. While the complete API can be found in the [Rustdoc][], this section will explain the most important parts. Please note that the API can change at any point and there are still some public functions which should actually be internal.

### Creating a virtual machine

Before you are able to do anything with the library, you will need to create a virtual machine. The virtual machine is responsible for running Gluon programs and can be created with the [new_vm][] function.

### Compiling and running gluon code

Once in possession of a [RootedThread][], you can compile and execute code using the [run_expr][] method on the [ThreadExt][] extension trait.

[ThreadExt]:https://docs.rs/gluon/*/gluon/trait.ThreadExt.html

```rust,ignore
let vm = new_vm();
let (result, _) = vm
    .run_expr::<i32>("example", "1 + 2")
    .ok();
assert_eq!(result, Some(3));
```

Notably, if we were to execute a script with side effects the code above will actually not run the side effects. To make gluon run side effects we need to set the [run_io][] flag on [ThreadExt][].

[run_io]:https://docs.rs/gluon/*/gluon/trait.ThreadExt.html#method.run_io

```rust,ignore
let vm = new_vm();

let script = r#"
let io = import! std.io
io.print "123"
"#;
// Returns an action which prints `123` when evaluated
vm.run_expr::<IO<()>>("example", script)
    .unwrap();
// Prints `123` to stdout
vm.run_io(true);
vm.run_expr::<IO<()>>(&vm, "example", script)
    .unwrap();
```

Often, it is either inconvenient or inefficient to compile and run code directly from source code. To write the above example in a more efficient way, we could instead load the `(+)` function and call it directly.

```rust,ignore
let vm = new_vm();
// Ensure that the prelude module is loaded before trying to access something from it
vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", r#" import! std.prelude "#)
    .unwrap();
let mut add: FunctionRef<fn (i32, i32) -> i32> = vm.get_global("std.prelude.num_Int.(+)")
    .unwrap();
let result = add.call(1, 2);
assert_eq!(result, Ok(3));
```

### Calling Rust functions from gluon

Gluon also allows native functions to be called from gluon. To do this we first need to define the function so it is available when running Gluon code.

```rust,ignore
fn factorial(x: i32) -> i32 {
    if x <= 1 {
        1
    } else {
        x * factorial(x - 1)
    }
}

fn load_factorial(vm: &Thread) -> vm::Result<vm::ExternModule> {
    vm::ExternModule::new(vm, primitive!(1, factorial))
}

let vm = new_vm();

// Introduce a module that can be loaded with `import! factorial`
add_extern_module(&vm, "factorial", load_factorial);

let expr = r#"
    let factorial = import! factorial
    factorial 5
"#;

let (result, _) = vm.run_expr::<i32>("factorial", expr)
    .unwrap();

assert_eq!(result, 120);
```

[add_extern_module][] can do more than just exposing simple functions. For instance, the [primitives][] module export large parts of Rust's [string][] and [float][] modules directly as records in Gluon under the `str` and `float` modules respectively.

```rust,ignore
let vm = new_vm();
let (result, _) = vm.run_expr::<String>("example", " let string  = import! \"std/string.glu\" in string.trim \"  Hello world  \t\" ")
    .unwrap();
assert_eq!(result, "Hello world");
```

[Rustdoc]:https://docs.rs/gluon/*/gluon/index.html
[new_vm]:https://docs.rs/gluon/*/gluon/fn.new_vm.html
[RootedThread]:https://docs.rs/gluon/*/gluon/struct.RootedThread.html
[Thread]:https://docs.rs/gluon/*/gluon/struct.Thread.html
[run_expr]:https://docs.rs/gluon/*/gluon/trait.ThreadExt.html#method.run_expr
[add_extern_module]:https://docs.rs/gluon/*/gluon/import/fn.add_extern_module.html
[primitives]:https://github.com/gluon-lang/gluon/blob/master/vm/src/primitives.rs
[string]:http://doc.rust-lang.org/std/primitive.str.html
[float]:http://doc.rust-lang.org/std/primitive.f64.html
