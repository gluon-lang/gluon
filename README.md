# embed_lang (working title)
[![Build Status](https://travis-ci.org/Marwes/embed_lang.svg?branch=master)](https://travis-ci.org/Marwes/embed_lang)

This library is a complete compiler and virtual machine for an embeddable langauge implemented in pure [Rust][Rust]. As both syntax and semantics are not fully nailed down yet it is not recommended for serious use.

## Usage

### REPL
There is a rudimentary REPL which can be used by passing the `-i` flag to the built repl executable which can be run through `cargo run -- -i`). The REPL is capable of:
* Evaluating expressions (expressions of type IO will be evaluated in the IO context).
* Printing help about available commands with `:h`
* Loading files with `:l path_to_file` the result of evaluating the expression in the loaded file is stored in a variable named after the filename without an extension.
* Checking the types of expressions with `:t expression`
*   Printing information about a name with `:i name`.<br>
    Example:

        :i std.prelude.List
        type std.prelude.List a = | Nil | Cons a (std.prelude.List a)
        /// A linked list type
        
* Exit the REPL by writing `:q`

## Documentation

[Tutorial (WIP)](https://github.com/Marwes/embed_lang/blob/master/TUTORIAL.md)

[Rustdoc](https://marwes.github.io/embed_lang/embed_lang/index.html)

## Examples

## Hello world

```f#
io.print "Hello world!"
```

## Factorial

```f#
let factorial n : Int -> Int =
    if n < 2
    then 1
    else n * factorial (n - 1)

factorial 10
```

### Syntax

Larger example which display most if not all of the syntactical elements in the language.

```f#
// `let` declares new variables.
let id x = x

let factorial n =
        if n < 2
        then 1
        else n * factorial (n - 1)

// `type` is used to declare a new type.
// In this case we declare `Countable` to be a record with a single field (count) which is a function
// taking a single arguemnt and returning an integer
type Countable a = { count: a -> Int }

// "Counting" an integer just means returning the integer itself
let countable_Int: Countable Int = { count = \x -> x }

let list_module =
    // Declare a new type which only exists in the current scope
    type List a = | Cons a (List a) | Nil
    let map f xs =
            case xs of
                | Cons y ys -> Cons (f y) (map f ys)
                | Nil -> Nil
    // Define a count instance over lists which counts each of the elements and sums
    // the results
    let countable_List c: Countable a -> Countable (List a) =
        let count xs =
            case xs of
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
let { count }: Countable (List Int) = countable_List countable_Int
if count (Cons 20 (Cons 22 Nil)) == 41 then
    error "This branch is not executed"
else
    io.print "Hello world!"
```

## Contributing

If you are interested in contributing to this project there are a few issues open marked as [beginner][] which should be possible to for someone unfamiliar with the code. If you find something that looks interesting leave a comment on the issue so I know about it annd can give some assistance if needed.

[beginner]:https://github.com/Marwes/embed_lang/labels/Beginner

## Goals/Features
These goals may change or be refined over time as I experiment with what is possible to with the language.

* **Embeddable** - Similiar to [Lua][Lua] it is meant to be able to be included in another program which can use the virtual machine to extend its own functionality.

* **Statically typed** - It currently uses the Hindley-Milner type system with some extensions.

* **Tiny** - The language should be as small as possible while still remaining practical. As having a static typesystem already demands a good chunk of extra code it becomes even more important to have a very small set of features as every feature added is likely to need code added to the parser, typechecker as well as the compiler causing even small additions to add a larger amount of code than it would in a dynamic language.

  As an example, there is no concept of modules as a concept of grouping code. Instead the basic records fills the same role (Caveat: Types currently always globally exported though this should change). Now instead of files being compiled as modules they are just expressions which return a record of the functions they export! See the [prelude][] for an example.

* **Strict** - Laziness is supported through an explicit type but being strict by default leads to easier to debug code.

* **Modular** - The library is split into parser, typechecker and virtual machine + compiler currently all of which can be used independently. Certain language agonstic things are also likely candidates for separation from the main library. For instance the garbage collector is currently quite unaware of the rest of the code and might be made into separate crate (if you see something useful separately from the library please don't hesitate to open an issue!).

[prelude]:https://github.com/Marwes/embed_lang/blob/master/std/prelude.hs

## Inspiration

This language takes its primary inspiration from [Lua][Lua], [Haskell][Haskell] and [OCaml][OCaml].

[Lua]: http://www.lua.org
[Haskell]: http://www.haskell.org
[OCaml]: http://www.ocaml.org
[Rust]: http://www.rust-lang.org
