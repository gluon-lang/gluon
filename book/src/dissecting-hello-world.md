# Dissecting Hello World

```gluon
let io = import! std.io
io.println "Hello world!"
```

There are a number of things going on in the hello world example so lets break them down one step at a time.

```gluon
let
```

Gluon uses the keyword `let` to bind values for later use.

```gluon
import! std.io
```

`import!` is a builtin macro which loads the contents of another module. In the example we use it to get access to the standard library's `io` module. Since it appeared on the right side of `let io =` we thus bound the `std.io` module to the `io` binding.

```
io.println
```

Here we access the `println` function from the `io` module we bound earlier which is a function that lets us write strings to stdout.

```gluon
"Hello world!"
```

Finally we create a string literal which gets passed to `println` to get printed.
