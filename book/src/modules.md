# Modules

## Importing modules

As is often the case, it is convenient to separate code into multiple files which can later be imported and used from multiple other files. To do this, we can use the `import!` macro which takes a single string literal as argument and loads and compiles that file at compile time before the importing module is compiled.

For example, say that we need the `assert` function from the `test` module which can be found at `std/test.glu`. We might write something like this:

```f#,rust
let { assert } = import! std.test
assert (1 == 1)
```

## Writing modules

Importing standard modules is all well and good but it is also necessary to write your own once a program starts getting too big for a single file. As it turns out, if you have been following along so far, you already know everything about writing a module! Creating and loading a module in gluon entails creating a file containing an expression which is then loaded and evaluated using `import!`. `import!` is then just the value of the evaluated expression.

```f#
// module.glu
type Named a = { name: String, value: a }
let twice f x = f (f x)
{ twice, Named }

//main.glu
let { twice, Named }  = import! "module.glu"
let addTwice = twice (\x -> x + 1)
let namedFloat : Named Float = { name = "pi", value = 3.14 }
addTwice 10
```

Though modules are most commonly a record, this does not have to be the case. If you wanted, you could write a module returning any other value as well.

```f#
// pi.glu
3.14

//main.glu
let pi  = import! "pi.glu"
2 * pi * 10
```

