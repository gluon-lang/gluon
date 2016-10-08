# The main repo of gluon has been moved to https://github.com/gluon-lang/gluon

# gluon

[![Build Status](https://travis-ci.org/gluon-lang/gluon.svg?branch=master)](https://travis-ci.org/gluon-lang/gluon) [![Gitter](https://badges.gitter.im/gluon-lang/gluon.svg)](https://gitter.im/gluon-lang/gluon?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge) [![Documentation](https://docs.rs/gluon/badge.svg)](https://docs.rs/crate/gluon)

Gluon is a small, statically-typed, functional programming language designed for application embedding.

## Features

* **Statically typed** - Static typing makes it easier to write safe and efficient interfaces between gluon and the host application.

* **Type inference** - Type inference ensures that types rarely have to be written explicitly giving the all the benefits of static types with none of the typing.

* **Simple embedding** - Marshalling values to and from gluon requires next to no boiler plate allowing functions defined in [Rust][] to be [directly passed to gluon][easy_embed].

* **UTF-8 by default** - Gluon supports unicode out of the box with utf-8 encoded strings and unicode codepoints as characters.

* **Separate heaps** - Gluon is a garbage collected language but uses a separate heap for each executing gluon thread. This keeps each heap small, reducing the overhead of the garbage collector.

* **Thread safe** - Gluon is written in Rust which guarantees thread safety and gluon keeps the same guarantees allowing multiple gluon programs to run in parallel ([example][parallel])\*

[easy_embed]:https://github.com/gluon-lang/gluon/blob/master/TUTORIAL.md#embedding-api
[parallel]:https://github.com/gluon-lang/gluon/blob/master/tests/parallel.rs

\* Parallel execution of gluon programs is a recent addition and may still have issues such as deadlocks.

## Usage

### Try online (WIP)

You can try gluon in your browser at the [try_gluon](http://ec2-52-29-1-213.eu-central-1.compute.amazonaws.com/) server.

### Installation

#### Rust

Gluon requires a recent Rust compiler to build (1.9.0 or later) and is available at [crates.io](https://crates.io/crates/gluon) and can easily be included in a Cargo project by adding the lines below.

```toml
[dependencies]
gluon = "0.2.0"
```

#### Other languages
Currently the easiest way to interact with the gluon virtual machine is through Rust but a rudimentary [C api][] exists which will be extended in the future to bring it closer to the Rust api.

[C api]: https://github.com/gluon-lang/gluon/blob/master/c-api/src/lib.rs

## Tools

### Visual Studio Code Extension

The [gluon extension][] for Visual Studio Code provides syntax highlighting and completion. To install it, search for `gluon` among the extensions.

![example](http://i.imgur.com/44bH0ww.gif)

[gluon extension]:https://marketplace.visualstudio.com/items?itemName=Marwes.gluon

### REPL

Gluon has a small executable which can be used to run gluon programs directly or to run a small REPL. The REPL can be started by passing the `-i` flag to the built repl executable which can be run through `cargo run -- -i`).

REPL features:
* Evaluating expressions (expressions of type IO will be evaluated in the IO context).
* Printing help about available commands with `:h`
* Loading files with `:l path_to_file` the result of evaluating the expression in the loaded file is stored in a variable named after the filename without an extension.
* Checking the types of expressions with `:t expression`
*   Printing information about a name with `:i name`.<br>
    Example:

        :i std.prelude.List
        type std.prelude.List a = | Nil | Cons a (std.prelude.List a)
        /// A linked list type

* Tab-completion of identifiers and record fields
    ![repl completion](http://i.imgur.com/IXLQFtV.gif)
* Exit the REPL by writing `:q`

## Documentation

[Tutorial (WIP)](https://github.com/gluon-lang/gluon/blob/master/TUTORIAL.md)

[Rustdoc](https://gluon-lang.github.io/gluon/gluon/index.html)

## Examples

## Hello world

```f#,rust
io.print "Hello world!"
```

## Factorial

```f#,rust
let factorial n : Int -> Int =
    if n < 2
    then 1
    else n * factorial (n - 1)

factorial 10
```

### Syntax

Larger example which display most if not all of the syntactical elements in the language.

```f#,rust
// `let` declares new variables.
let id x = x

let factorial n =
        if n < 2
        then 1
        else n * factorial (n - 1)

// `type` is used to declare a new type.
// In this case we declare `Countable` to be a record with a single field (count) which is a function
// taking a single argument and returning an integer
type Countable a = { count : a -> Int }

// "Counting" an integer just means returning the integer itself
let countable_Int : Countable Int = { count = \x -> x }

let list_module =
    // Declare a new type which only exists in the current scope
    type List a = | Cons a (List a) | Nil
    let map f xs =
            match xs with
                | Cons y ys -> Cons (f y) (map f ys)
                | Nil -> Nil
    // Define a count instance over lists which counts each of the elements and sums
    // the results
    let countable_List c : Countable a -> Countable (List a) =
        let count xs =
            match xs with
            | Cons y ys -> c.count y + count ys
            | Nil -> 0
        { count }
    {
        // Since `List` is local we export it so its constructors can be used
        // outside the current scope
        List,
        countable_List,
        map
    }

// Bring the `List` type and its constructors into scope
let { List, countable_List } = list_module

// Create a `Countable` record for `List Int`
let { count } : Countable (List Int) = countable_List countable_Int

if count (Cons 20 (Cons 22 Nil)) == 41 then
    error "This branch is not executed"
else
    io.print "Hello world!"
```

## Contributing

There are many ways to contribute to gluon. The two simplest ways of starting out is opening issues or working on an issue marked as [beginner][]. For more extensive information about contributing you can look at [CONTRIBUTING.md][].

[beginner]:https://github.com/gluon-lang/gluon/labels/Beginner
[CONTRIBUTING.md]:https://github.com/gluon-lang/gluon/blob/master/CONTRIBUTING.md

## Goals
These goals may change or be refined over time as I experiment with what is possible to with the language.

* **Embeddable** - Similiar to [Lua][Lua] it is meant to be able to be included in another program which can use the virtual machine to extend its own functionality.

* **Statically typed** - The language uses a Hindley-Milner based type system with some extensions which allows for simple and general type inference.

* **Tiny** - By being tiny the langauge is easy to learn and makes the implementation small.

* **Strict** - Strict languages are usually easier to reason about, especially considering that is what most people are accustomed with. For cases where lazines is desired an explict type is provided.

* **Modular** - The library is split into parser, typechecker and virtual machine + compiler. Each of these components can be use independently of each other allowing applications to pick and choose exactly what they need.

[prelude]:https://github.com/gluon-lang/gluon/blob/master/std/prelude.glu

## Inspiration

This language takes its primary inspiration from [Lua][Lua], [Haskell][Haskell] and [OCaml][OCaml].

[Lua]: http://www.lua.org
[Haskell]: http://www.haskell.org
[OCaml]: http://www.ocaml.org
[Rust]: http://www.rust-lang.org
