# Tutorial

(Everything is TODO here but some parts are more TODO than others...)

## Introduction

This tutorial aims the explain the basics of embed_lang's syntax and semantics.


## Hello world

In traditional form we will begin with the classic hello world program.

```f#
io.print "Hello world"
```

## Syntax and semantics

embed_lang is a functional language at heart, basing its syntax on languages such as F#, OCaml and Haskell.
The syntax may thus look strange if you are coming from C-like languages but don't be discouraged!
There is actually very little syntax to learn.................
Something, something know functional syntax


### Identifiers and Literals

The simplest syntactical elements in embed_lang are identifiers and literals and none of them should be especially 
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

Another way of calling a function is through infix notation since embed_lang implements all operators as just functions.

```f#
1 + 2 // Calls the + function on 1 and 2
```
```f#
(+) 1 2 // Parenthesizing an operator makes it possible to use in a normal function call
```

It is important to note that function application binds harder than any binary operator.

```f#
(+) 0 1 - (+) 2 3 // Equivalent to (0 + 1) - (2 + 3)
```

### Variable bindings

Any language more complex than Hello world is bound to require variable bindings which serve to bind some value to a name
allowing it to be used later.

```f#
let x = 1 + 2 in x // Returns 3
```

You may rightly be wondering about the `in x` part. embed_lang takes a strong stance against statements in an effort to keep
things consistent. Thus only writing `let x = 1 + 2` will be met with a syntax error about a missing `in` keyword which is
what defines the actual value returned from the `let` expression.

Let bindings also allow functions to be defined which is done by listing the arguments between the bound identifier and `=`

```f#
// Defines the `id` function which takes a single argument and returns it.
let id x = x in id 1 // Returns 1
```

Mutually recursive functions can be defined using `let` by writing `and` before each successive binding.

```f#
let f x = g x
and g x = f x
in f 1 // Never returns
```

## If expressions

The simplest control flow expression is the `if` expression which evaluates a boolean expression and then takes the
first branch if the boolean is evaluated to `True` and the second if it evaluates to `False`

```f#
if True then 1 else 0
```

## Record expressions

To create more complex data types embed_lang has first class records which can be used to group data which belong together easily.

```f#
{ pi = 3.14, add = (+) }
```

To access the fields of a record `.` is used.

```f#
let record = { pi = 3.14, add = (+) }
record.pi // Returns 3.14
```

The assignment to a field can be omitted if there is a variable in scope with the same name as the field.

```f#
let id x = x
{ id }
```

## Variants

While records are great for grouping related data together there is often a need to have data which can be one of several variants. Unlike records, variants need to be defined before their use.

```f#
type Option a = | Some a | None
Some 1
```

## Case expressions

To allow variants to be unpacked so that their contents can be retrieved embed_lang has the `case` expression.

```f#
match None with
| Some x -> x
| None -> 0
```

Here we write out a pattern for each of the variant's constructors and the value we pass in (`None` in this case) is matched to each of these patterns. When a matching pattern is found the expression on the right of `->` is evaluated with each of the constructor's arguments bound to variables.

`case` expressions can also be used to unpack records.

```f#
match { x = 1.0, pi = 3.14 } with
| { x = y, pi } -> y + pi
```

`let` bindings can also unpack records letting the expression above be written as.

```f#
let { x = y, pi } = { x = 1.0, pi = 3.14 }
in y + pi
```

## Type expressions

embed_lang allows new types to be defined through the `type` expression.

```f#
// type <identifier> <identifier>* = <type> in <expression>
type Option a = | None | Some a
in 0
```

`type` requires `in <expression>` just like `let` to ensure that that a value is returned. Mutually recursive types can
be defined by writing `and` between each definition.

```f#
type SExpr_ = | Atom String | Cons SExpr SExpr
and SExpr = { location: Int, expr: SExpr_ }
in Atom "name"
```

### Type syntax (TODO)

#### Function types

```
<type> -> <type>
```

#### Record type

```
{ (<identifier> : <type>)* }
{ pi: Float, sin: Float -> Float }
```

#### Enumeration type

```
( | <identifier> (<type>)* )* 

| Err e | Ok t
```

#### Alias type

```
<identifier> (<type>)*
Int
Float
Option Int
```

## Indentation

TODO Better explanation

If you have been following along this far you may be thinking think that syntax so far is pretty limiting. In particular you wouldn't be wrong in thinking that the `let` and `type` syntax are clunky due to their need to be closed by the `in` keyword. Luckily embed_lang offerrs a more convenient way of writing bindings by relying on indentation.

When a token starts on the same line as a token on an earlier line, embed_lang implicitly adds inserts a block expression which allows multiple expressions and bindings to be run sequentially with all variables in scope.

```f#
let id x = x
id 1 // `in` can be omitted since `id 1` starts on the same line as `let`
```

```f#
do_something1 ()
do_something2 ()
type PrivateType = | Private Int
let x = Private (do_something3 ())
match x with
| Private y -> do_something4 x
```

Indented blocks can can be used to limit the scope of some variables.

```f#
let module =
    let id x = x
    type MyInt = Int
    { MyInt, id, pi = 3.14 }

module.id module.pi

// The above is equivalent to

let module =
    let id x = x
    in { id, pi = 3.14 }
in
module.id module.pi
```

## Lambda expressions

While we have seen that functions can be defined in let expressions it is often valuable to define a function without giving it an explicit name.

```f#
// \(<identifier)* -> <expr>
\x y -> x + y - 10
// Equivalent to
let f x y = x + y - 10 in f
```

## Importing modules

As is often the case it is convenient to separate code into multiple files which can later be imported and used from multiple other files. To do this we can use the import macro which takes a single string literal as argument and loads that file at compile time before the module importing it gets compiled.

So say that we need the `assert` function from the `test` module which can be found at `std/test.hs`. Then we might write something like this.

```f#
let { assert } = import "std/test.hs"
assert (1 == 1)
```

## Writing modules

Importing standard modules is all well and good but it is also necessary to write your own once a program starts getting to big for a single file. As it turns out, if you have been following along so far, you already know everything about writing a module! Creating and loading a module in embed_lang just entails writing creating a file containing an expression which is then loaded and evaluated using `import`. `import` is then just the value of evaluating the expression.

```f#
// module.hs
type Named a = { name: String, value: a }
let twice f x = f (f x)
{ twice, Named }

//main.hs
let { twice, Named } = import "module.hs"
let addTwice = twice (\x -> x + 1)
let namedFloat: Named Float = { name = "pi", value = 3.14 }
addTwice 10
```

Though modules are most commonly a record this does not have to be the case. If you wanted you could write a module returning any other value as well.

```f#
// pi.hs
3.14

//main.hs
let pi = import "pi.hs"
2 * pi * 10
```

## Standard types and functions

https://github.com/Marwes/embed_lang/tree/master/std

TODO

### Prelude

When compiling a an expression the compiler automatically inserts a small prelude before the expression itself which gives automatic access to basic operators such as `+`, `-`, etc as well as types such as `Option` and `Result`.

### Threads and channels

embed_lang has support for cooperative threading and communication between them through the `Thread` and `Channel` types.

TODO
