# Tutorial

[Introduction](#introduction)

[Syntax and semantics](#syntax-and-semantics)

[Indentation](#indentation)

[Importing modules](#importing-modules)

[Writing modules](#writing-modules)

[Embedding API](#embedding-api)

[Standard types and functions](#standard-types-and-functions)

## Introduction

This tutorial aims the explain the basics of gluon's syntax and semantics.

## Hello world

In traditional form we will begin with the classic hello world program.

```f#,rust
io.println "Hello world"
```

## Syntax and semantics

gluon is a functional language at heart, basing its syntax on languages such as F#, OCaml and Haskell.
The syntax may thus look strange if you are coming from C-like languages but don't be discouraged!
There is actually very little syntax to learn.

If, on the other hand, you are familiar with functional languages you will be right at home. Roughly speaking, gluon takes the expression syntax from F# and OCaml but uses the type syntax of Haskell.

### Identifiers and Literals

The simplest syntactical elements in gluon are identifiers and literals and none of them should be especially
surprising if you are experienced in programming. Identifiers are a sequence of alphanumeric characters including
underscore ('_') which has to start with a letter or an underscore. Literals come in four different forms
integer, float, string and character literals.

```f#
// An identifier
abc123_
// An integer literal
42
// A float literal
3.14
// A string literal
"Hello world"
// A character literal
'e'
```

### Comments

Comments should be immediately familiar if you are accustomed to C-like languages. `//` starts a line comment which is ended
by a newline and `/*` starts a block comment which is ended by `*/`.

### Functions

```f#
f x "argument" 3
```

Being a functional language functions are everywhere and because of this calling functions have an intentional minimalistic
syntax where there is no need to enclose the arguments in a parenthesized list of arguments. Instead arguments are just
separated by whitespace.

Another way of calling a function is through infix notation since gluon implements all operators as just functions.

```f#,rust
1 + 2 // Calls the + function on 1 and 2
```
```f#,rust
(+) 1 2 // Parenthesizing an operator makes it possible to use in a normal function call
```

It is important to note that function application binds harder than any binary operator.

```f#,rust
(+) 0 1 - (+) 2 3 // Equivalent to (0 + 1) - (2 + 3)
```

### Variable bindings

Any language more complex than Hello world is bound to require variable bindings which serve to bind some value to a name
allowing it to be used later.

```f#,rust
let x = 1 + 2 in x // Returns 3
```

You may rightly be wondering about the `in x` part. gluon takes a strong stance against statements in an effort to keep
things consistent. Thus only writing `let x = 1 + 2` will be met with a syntax error about a missing `in` keyword which is
what defines the actual value returned from the `let` expression.

Let bindings also allow functions to be defined which is done by listing the arguments between the bound identifier and `=`

```f#,rust
// Defines the `id` function which takes a single argument and returns it.
let id x = x in id 1 // Returns 1
```

Mutually recursive functions can be defined using `let` by writing `and` before each successive binding.

```f#
let f x = g x
and g x = f x
in f 1 // Never returns
```

### If expressions

The simplest control flow expression is the `if` expression which evaluates a boolean expression and then takes the
first branch if the boolean is evaluated to `True` and the second if it evaluates to `False`

```f#,rust
if True then 1 else 0
```

### Record expressions

To create more complex data types gluon has first class records which can be used to group data which belong together easily.

```f#,rust
{ pi = 3.14, add1 = (+) 1.0 }
```

To access the fields of a record `.` is used.

```f#,rust
let record = { pi = 3.14, add1 = (+) 1.0 }
in record.pi // Returns 3.14
```

The assignment to a field can be omitted if there is a variable in scope with the same name as the field.

```f#,rust
let id x = x
in { id }
```

### Variants

While records are great for grouping related data together there is often a need to have data which can be one of several variants. Unlike records, variants need to be defined before they can be used.

```f#,rust
type MyOption a = | Some a | None
Some 1
```

### Case expressions

To allow variants to be unpacked so that their contents can be retrieved gluon has the `case` expression.

```f#,rust
match None with
| Some x -> x
| None -> 0
```

Here we write out a pattern for each of the variant's constructors and the value we pass in (`None` in this case) is matched to each of these patterns. When a matching pattern is found the expression on the right of `->` is evaluated with each of the constructor's arguments bound to variables.

`case` expressions can also be used to unpack records.

```f#,rust
match { x = 1.0, pi = 3.14 } with
| { x = y, pi } -> y + pi
```

`let` bindings can also unpack records letting the expression above be written as.

```f#,rust
let { x = y, pi } = { x = 1.0, pi = 3.14 }
in y + pi
```

### Lambda expressions

While we have seen that functions can be defined in let expressions it is often valuable to define a function without giving it an explicit name.

```f#,rust
// \(<identifier)* -> <expr>
\x y -> x + y - 10
// Equivalent to
let f x y = x + y - 10 in f
```

### Type expressions

gluon allows new types to be defined through the `type` expression which just like `let` requires `in <expression>` to be written at the end to ensure it returns a value.

```f#,rust
// type <identifier> <identifier>* = <type> in <expression>
type MyOption a = | None | Some a
let divide x y : Int -> Int -> MyOption Int =
    if (x / y) * y == x then
        Some (x / y)
    else
        None
in divide 10 4
```

An important difference from many languages however is that `type` only defines aliases. This means that all types in the example below are actually equivalent to each other.

```f#,rust
type Type1 = { x: Int }
type Type2 = Type1
type Type3 = { x: Int }
let r1 : Type1 = { x = 0 }
let r2 : Type2 = r1
let r3 : Type3 = r2
in r1
```

Mutually recursive types can be defined by writing `and` between each definition.

```f#,rust
type SExpr_ = | Atom String | Cons SExpr SExpr
and SExpr = { location: Int, expr: SExpr_ }
in Atom "name"
```

### Indentation

If you have been following along this far you may be thinking think that the syntax so far is pretty limiting. In particular you wouldn't be wrong in thinking that the `let` and `type` syntax are clunky due to their need to be closed by the `in` keyword. Luckily gluon offers a more convenient way of writing bindings by relying on indentation.

When a token starts on the same column as an unclosed `let` or `type` expression the lexer implicitly inserts an `in` token which closes the declaration part and makes the following expression into the body.

```f#,rust
let add1 x = x + 1
add1 11 // `in` will be inserted automatically since `add1 11` starts on the same line as the opening `let`
```

If a token starts on the same column as an earlier expression but there is not an unclosed `type` or `let` expression gluon treats the code as a block expression which means each expression are run sequentially, returning the value of the last expression.

```f#
do_something1 ()
do_something2 () // `do_something1 ()` is run, then `do_something_2`. The result of `type ...` is the result of the expression
type PrivateType = | Private Int
let x = Private (do_something3 ())
do_something3 ()
match x with
| Private y -> do_something4 x
```

Indented blocks can can be used to limit the scope of some variables.

```f#,rust
let module =
    let id x = x
    type MyInt = Int
    { MyInt, id, pi = 3.14 }

module.id module.pi
```
Which is equivalent to:
```f#,rust
let module =
    let id x = x
    in
    type MyInt = Int
    in { id, pi = 3.14 }
in
module.id module.pi
```

## Typesystem

### Function types

```
<type> -> <type>
```

Function types are written using the `(->)` operator which is right associative. This means that the function type `Int -> (Int -> Int)` (A function taking one argument of Int and returning a function of `Int -> Int`) can be written as `Int -> Int -> Int`.

### Record type

```
{ (<identifier> <identifier>* = <type>,)* (<identifier> : <type>,)* }
{ pi : Float, sin : Float -> Float }
```

Records are gluon's main way of creating associating related data and they should look quite familiar if you are familiar with dynamic languages such as javascript. Looks can be deceiving however as gluon's records are more similar to a struct in Rust or C as the order of the fields are significant, `{ x : Int, y : String } != { y : String, x : Int }`. Furthermore records are immutable meaning fields cannot be added or removed and the values within cannot be modified.

In addition to storing values, records also have a secondary function of storing types which is gluon's way of exporting types. If you have used modules in an ML language this may look rather familiar, looks can be deceiving however as 'type fields' must match exactly in gluon which means there is no subtyping relationship between records (`{ Test = { x : Int } }` is not a subtype of `{ Test = Float }`). This may change in the future.

```f#
{ Test = { x : Int } }
```

### Enumeration type

```
( | <identifier> (<type>)* )*

| Err e | Ok t
```

Gluon also has a second way of grouping data which is the enumeration type which allows you to represent a value being one of several variants. In the example above is the representation of gluon's standard `Result` type which represents either the value having been successfully computed (`Ok t`) or that an error occurred (`Err e`).

### Alias type

```
<identifier> (<type>)*
Int
Float
Option Int
Ref String
```

The last kind of type which gluon has is the alias type. An alias type is a type which explicitly names some underlying type which can either be one of the three types mentioned above or an abstract type which is the case for the `Int`, `String` and `Ref` types. If the underlying type is abstract then the type is only considered equivalent to itself (ie if you define an abstract type of `MyInt` which happens to have the same representation as `Int` the typechecker will consider these two types as being distinct).

### Higher-kinded types

Higher-kinded types are a fairly abstract concept in gluon and you may very well create entire programs without any knowledge about them. Sometimes they are a very valuable tool to have as they can be used to create very powerful abstractions.

Just as all values such as `0 : Int`, `"Hello World!" : String` and `Some 4.0 : Option Float` each have a type these types themselves have their own 'type' or the 'kind' as it is called. For the types of concrete values the `Kind` is always `Type` so for the earlier examples `Int : Type`, `String : Type` and `Option Float : Type`. That is not very useful on its own but it becomes more interesting when we consider the kind of `Option : Type -> Type`. `Type -> Type` looks rather like the type of a functions such as `show_int : Int -> String` but instead of taking a value it takes a type and produces a new type. In effect this lets us abstract over types instead of just over values. This abstraction facility can be seen in the `Functor : (Type -> Type) -> Type` type which takes a type with kind `Type -> Type` as argument which is exactly the kind of `Option` (or `List`, `Result a`).

### Overloading

Sometimes there there is a need to overload a name with multiple differing implementations and let the compiler chose the correct implementation. If you have written any amount of Gluon code so far you are likely to have already encountered this with numeric operators such as `(+)` or comparison operators such as `(==)`. While these operators are core parts of gluon they are not special cased by the compiler which lets you define and use overloaded bindings yourself.

To explain how overloading works first look at the example below where `show_type` has two implementations, one which takes an `Int` and one which takes a `Float`.

```f#,rust
let show_type _ : Int -> String = "Int"
let show_type _ : Float -> String = "Float"

show_type 0 // Returns "Int"
show_type 0.0 // Returns "Float"
// show_type "" // Would be a type error
```

When the typechecker encounters the second `show_type` binding in this example it does not simply shadow the first binding as is common in many programming languages. Instead the typechecker checks the type of the binding already in scope and calculates the 'intersection' of the two bindings. In the example above the first binding has the type `Int -> String` while the second is `Float -> String`. By calculating the 'intersection' the typechecker calculates the most specialized type which both bindings can still successfully unify to which in this case is `a -> String`. Any subsequent use of `show_type` will then be observed as `a -> String` which succeeds with both a `Int` and `Float` argument.

Unfortunately it would also succeed if a `String` (or any other) type were used as the argument which is not acceptable as we have only implemented `show_type` for `Int` and `Float`. To catch this case (and to figure out which overload should be use where) the typechecker does an extra pass after successfully typechecking the entire expression. In this pass all uses of overloaded bindings are checked against the overload candidates until a match is found. Thus the third call, were it not commented out, would produce an error as there is no overloaded binding matching the type `String -> String`.

## Importing modules

As is often the case it is convenient to separate code into multiple files which can later be imported and used from multiple other files. To do this we can use the `import` macro which takes a single string literal as argument and loads and compiles that file at compile time before the importing module is compiled.

So say that we need the `assert` function from the `test` module which can be found at `std/test.glu`. Then we might write something like this.

```f#,rust
let { assert } = import "std/test.glu"
assert (1 == 1)
```

## Writing modules

Importing standard modules is all well and good but it is also necessary to write your own once a program starts getting to big for a single file. As it turns out, if you have been following along so far, you already know everything about writing a module! Creating and loading a module in gluon just entails writing creating a file containing an expression which is then loaded and evaluated using `import`. `import` is then just the value of evaluating the expression.

```f#
// module.glu
type Named a = { name: String, value: a }
let twice f x = f (f x)
{ twice, Named }

//main.glu
let { twice, Named } = import "module.glu"
let addTwice = twice (\x -> x + 1)
let namedFloat : Named Float = { name = "pi", value = 3.14 }
addTwice 10
```

Though modules are most commonly a record this does not have to be the case. If you wanted you could write a module returning any other value as well.

```f#
// pi.glu
3.14

//main.glu
let pi = import "pi.glu"
2 * pi * 10
```

## Embedding API

The API with which the host language interacts with gluon is very important part of the library. While the complete API can be found in the [Rustdoc][] this section will explain the most important parts. Please note that the API can change at any point and there are still some public functions which should actually be internal.

### Creating a virtual machine

Before you are able to do anything with the library you will need to create a virtual machine. The virtual machine is responsible for running gluon programs and can be created with the [new_vm][] function.

### Compiling and running gluon code

Once in possession of a [RootedThread][] you can compile and execute code using the [run_expr][] method on the [Compiler][] builder type.

```rust,ignore
let vm = new_vm();
let (result, _) = Compiler::new()
    .run_expr::<i32>(&vm, "example", "1 + 2")
    .ok();
assert_eq!(result, Some(3));
```

Often it is either inconvenient or inefficient to compile and run code directly from source code. To write the above example in a more efficient way we could instead load the `(+)` function and call it directly.

```rust,ignore
let vm = new_vm();
// Ensure that the prelude module is loaded before trying to access something from it
Compiler::new()
    .run_expr::<Generic<A>>(&vm, "example", " import \"std/prelude.glu\" ")
    .unwrap();
let mut add: FunctionRef<fn (i32, i32) -> i32> = vm.get_global("std.prelude.num_Int.(+)")
    .unwrap();
let result = add.call(1, 2);
assert_eq!(result, Ok(3));
```

### Calling Rust functions from gluon

gluon also allows native functions to be called from gluon. To do this we first need to define the function so it is available when running gluon code.

```rust,ignore
fn factorial(x: i32) -> i32 {
    if x <= 1 { 1 } else { x * factorial(x - 1) }
}
let vm = new_vm();
vm.define_global("factorial", factorial as fn (_) -> _)
    .unwrap();
let (result, _) = Compiler::new()
    .run_expr::<i32>(&vm, "example", "factorial 5")
    .unwrap();
assert_eq!(result, 120);
```

[define_global][] can do more than just exposing simple functions. For instance, the [primitives][] module export large parts of Rust's [string][] and [float][] modules directly as records in gluon under the `str` and `float` modules respectively.

```rust,ignore
let vm = new_vm();
let (result, _) = Compiler::new()
    .run_expr::<String>(&vm, "example", " let string = import \"std/string.glu\" in string.trim \"  Hello world  \t\" ")
    .unwrap();
assert_eq!(result, "Hello world");
```

[Rustdoc]:https://marwes.github.io/gluon/gluon/index.html
[new_vm]:https://marwes.github.io/gluon/gluon/fn.new_vm.html
[RootedThread]:https://marwes.github.io/gluon/gluon/struct.RootedThread.html
[Thread]:https://marwes.github.io/gluon/gluon/struct.Thread.html
[run_expr]:https://marwes.github.io/gluon/gluon/struct.Compiler.html#method.run_expr
[Compiler struct]:https://marwes.github.io/gluon/gluon/struct.Compiler.html
[define_global]:https://marwes.github.io/gluon/vm/thread/struct.Thread.html#method.define_global
[primitives]:https://github.com/Marwes/gluon/blob/master/vm/src/primitives.rs
[string]:http://doc.rust-lang.org/std/primitive.str.html
[float]:http://doc.rust-lang.org/std/primitive.f64.html

## Standard types and functions

https://github.com/Marwes/gluon/tree/master/std

TODO

### Prelude

When compiling a an expression the compiler automatically inserts a small prelude before the expression itself which gives automatic access to basic operators such as `+`, `-`, etc as well as types such as `Option` and `Result`.

### Threads and channels

gluon has support for cooperative threading and communication between them through the `Thread` and `Sender`/`Receiver` types.

TODO
