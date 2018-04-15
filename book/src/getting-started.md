# Getting started

To get started with gluon we must first have a way to compile and run Gluon programs. The fastest way to get that is to download one of the pre-built binaries for Linux, Windows, OSX or FreeBSD from https://github.com/gluon-lang/gluon/releases. Alternatively, if you have a Rust compiler and Cargo installed you may install it with `cargo install gluon_repl`.

Once installed you can verify that it works by saving the following program into a file named `hello_world.glu` and then compile and run it with `gluon hello_world.glu`.

```gluon
let io = import! std.io
io.println "Hello world!"
```

If everything works the program should have printed `Hello world!` to your terminal.
