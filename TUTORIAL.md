# Tutorial

(Everything is TODO here but some parts are more TODO than others...)

## Introduction

This tutorial aims the explain the basics of embed_lang's syntax and semantics.


## Hello world

In traditional form we will begin with the classic hello world program.

```
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

```
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

```
f x "argument" 3
```

Being a functional language functions are everywhere and because of this calling functions have an intentional minimalistic
syntax where there is no need to enclose the arguments in a parenthesized list of arguments. Instead arguments are just 
separated by whitespace.

Another way of calling a function is through infix notation since embed_lang implements all operators as just functions.

```
1 + 2 // Calls the + function on 1 and 2
```
```
(+) 1 2 // Parenthesizing an operator makes it possible to use in a normal function call
```

It is also important to recognize that function application binds harder than any binary operator.

```
(+) 0 1 - (+) 2 3 // Equivalent to (0 + 1) - (2 + 3)
```

### Variable bindings

Any language more complex than Hello world is bound to require variable bindings which serve to bind some value to a name
allowing it to be used later.

```
let x = 1 + 2 in x // Returns 3
```

You may rightly be wondering about the `in x` part. embed_lang takes a strong stance against statements in an effort to keep
things consistent. Thus only writing `let x = 1 + 2` will be met with a syntax error about a missing `in` keyword which is
what defines the actual value returned from the `let` expression.

Let bindings also allow functions to be defined which is done by listing the arguments between the bound identifier and `=`

```
// Defines the `id` function which takes a single argument and returns it.
let id x = x in id 1 // Returns 1
```

Mutually recursive functions can also be defined using `let` by writing `and` between each binding.

```
let f x = g x
and g x = f x
in f 1 // Never returns
```

## Record expressions

TODO

To support grouping of data elements embed_lang has first class record.

```
{ pi = 3.14, add = (+) }
```

The assignment can be omitted if there is a variable in scope with the same name as the field.

```
let id x = x
{ id }
```

## If expressions

The simplest control flow expression is the `if` expression which evaluates a boolean expression and then takes the
first branch if the boolean is evaluated to `True` and the second if it evaluates to `False`

```
if True then 1 else 0
```

## Case expressions


embed_lang also has `case` expressions which allow values to be branched on and unpacked.

### Patterns

### Variant pattern

Variants can be unpacked through `case` expressions by writing the variants name followed by an identifier for each
of its arguments.

```
case Some 1 of
| Some x -> x
| None -> 0
```

### Variant pattern

TODO
Records can be unpacked but not branched on

```
case { x = 1.0, pi = 3.14 } of
| { x = y, pi } -> y + pi
```

`let` bindings can unpack records letting the expression above be written as.

```
let { x = y, pi } = { x = 1.0, pi = 3.14 }
in y + pi
```

## Type expressions

embed_lang allows new types to be defined through the `type` expression.

```
// type <identifier> <identifier>* = <type> in <expression>
type Option a = | None | Some a
in 0
```

`type` requires `in <expression>` just like `let` to ensure that that a value is returned. Mutually recursive types can
be defined by writing `and` between each definition.

```
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

If you have been following along this far you may be starting to think that the `let` and `type` syntax seem pretty clunky and
you wouldn't be wrong. While it is possible to use the syntax given above and it shouldn't be dismissed outright embed_lang does
have a more convenient way to write bindings by relying on indentation.

When writing an expression which starts on the same line as the `let` or `type` binding above, embed_lang allows the `in`
expression to be omitted.

```
let id x = x
id 1 // `in` can be omitted since `id 1` starts on the same line as `let`
```

Same thing works for for indented lines.
```
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

TODO

```
// \(<identifier)* -> <expr>
\x y -> x + y - 10
```

## Importing modules

TODO

## Writing modules

TODO

## Standard types and functions

TODO

### Prelude

TODO

### Threads and channels

TODO
