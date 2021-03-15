# gluon

[![Build Status](https://travis-ci.org/gluon-lang/gluon.svg?branch=master)](https://travis-ci.org/gluon-lang/gluon) [![Gitter](https://badges.gitter.im/gluon-lang/gluon.svg)](https://gitter.im/gluon-lang/gluon?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge) [![crates.io](https://meritbadge.herokuapp.com/gluon)](https://crates.io/crates/gluon)  [![Documentation](https://docs.rs/gluon/badge.svg)](https://docs.rs/crate/gluon) [![Book](https://img.shields.io/badge/gluon-book-yellow.svg)](https://gluon-lang.org/doc/crates_io/book/index.html) [![std](https://img.shields.io/badge/gluon-std-green.svg)](http://gluon-lang.org/doc/nightly/std/index.html)

Gluon is a small, statically-typed, functional programming language designed for application embedding.

## Features

* **Statically-typed** - Static typing makes it easier to write safe and efficient interfaces between gluon and the host application.

* **Type inference** - Type inference ensures that types rarely have to be written explicitly giving all the benefits of static types with none of the typing.

* **Simple embedding** - Marshalling values to and from gluon requires next to no boilerplate, allowing functions defined in [Rust][] to be [directly passed to gluon][easy_embed].

* **UTF-8 by default** - Gluon supports Unicode out of the box with utf-8 encoded strings and Unicode codepoints as characters.

* **Separate heaps** - Gluon is a garbage-collected language but uses a separate heap for each executing gluon thread. This keeps each heap small, reducing the overhead of the garbage collector.

* **Thread-safe** - Gluon is written in Rust, which guarantees thread safety. Gluon keeps the same guarantees, allowing multiple gluon programs to run in parallel ([example][parallel])\*

[easy_embed]:https://gluon-lang.org/doc/crates_io/book/embedding-api.html
[parallel]:https://github.com/gluon-lang/gluon/blob/master/tests/parallel.rs

\* Parallel execution of gluon programs is a recent addition and may still have issues such as deadlocks.

## Examples

### Hello world

```f#,rust
let io = import! std.io
io.print "Hello world!"
```

### Factorial

```f#,rust
let factorial n : Int -> Int =
    if n < 2
    then 1
    else n * factorial (n - 1)

factorial 10
```

### 24

[24 game]:https://github.com/gluon-lang/gluon/blob/master/examples/24.glu
```f#,rust,ignore
// # 24
//
// From http://rosettacode.org/wiki/24_game
//
// Write a program that randomly chooses and displays four digits, each from 1 ──► 9 (inclusive) with repetitions allowed.
//
// The program should prompt for the player to enter an arithmetic expression using just those, and all of those four digits, used exactly once each. The program should check then evaluate the expression.
//
// The goal is for the player to enter an expression that (numerically) evaluates to 24.
//
// * Only the following operators/functions are allowed: multiplication, division, addition, subtraction
// * Division should use floating point or rational arithmetic, etc, to preserve remainders.
// * Brackets are allowed, if using an infix expression evaluator.
// * Forming multiple digit numbers from the supplied digits is disallowed. (So an answer of 12+12 when given 1, 2, 2, and 1 is wrong).
// * The order of the digits when given does not have to be preserved.
//
//
// ## Notes
//
//     The type of expression evaluator used is not mandated. An RPN evaluator is equally acceptable for example.
//     The task is not for the program to generate the expression, or test whether an expression is even possible.


// The `import!` macro are used to load and refer to other modules.
// It gets replaced by the value returned by evaluating that module (cached of course, so that
// multiple `import!`s to the same module only evaluates the module once)
let io @ { ? } = import! std.io
let prelude = import! std.prelude
let { Result } = import! std.result
let array @ { ? } = import! std.array
let int = import! std.int
let string = import! std.string
let list @ { List, ? } = import! std.list
let random = import! std.random
let string = import! std.string

// Since imports in gluon returns regular values we can load specific parts of a module using pattern matches.
let char @ { ? } = import! std.char

let { (<>) } = import! std.semigroup
let { flat_map } = import! std.monad

let { (*>), (<*), wrap } = import! std.applicative

let { for } = import! std.traversable

type Op = | Add | Sub | Div | Mul
type Expr = | Int Int | Binop Expr Op Expr

let parse : String -> Result String Expr =
    // Gluon has a small parser combinator library which makes it easy to define an expression parser
    let parser @ {
        between,
        satisfy,
        satisfy_map,
        spaces,
        token,
        digit,
        skip_many1,
        recognize,
        lazy_parser,
        chainl1,
        (<?>),
        ? } = import! std.parser
    let { (<|>) } = import! std.alternative

    let lex x = x <* spaces

    let integer =
        // `do` expression provide a way to write monads in a way similiar to procedural code
        do i = lex (recognize (skip_many1 digit))
        match int.parse i with
        | Ok x -> wrap x
        | Err _ -> parser.fail "Unable to parse integer"

    let operator =
        satisfy_map (\c ->
            match c with
            | '*' -> Some Mul
            | '+' -> Some Add
            | '-' -> Some Sub
            | '/' -> Some Div
            | _ -> None)
            <?> "operator"

    rec
    let atom _ =
        parser.functor.map Int integer
            <|> between (lex (token '(')) (lex (token ')')) (lazy_parser expr)

    let binop _ =
        let op_parser =
            do op = lex operator
            wrap (\l r -> Binop l op r)
        chainl1 (atom ()) op_parser

    let expr _ = binop ()
    in

    // Gluon makes it possible to partially apply functions which we use here to scope all parser functions
    // inside the `let parse` binding above.
    let parse : String -> Result String Expr = parser.parse (expr () <* spaces)
    parse

/// Validates that `expr` contains exactly the same integers as `digits`
let validate digits expr : Array Int -> Expr -> Bool =
    let integers xs expr : List Int -> Expr -> List Int =
        match expr with
        | Int i -> Cons i xs
        | Binop l _ r -> integers (integers xs l) r
    let ints = integers Nil expr

    list.sort (list.of digits) == list.sort ints

let eval expr : Expr -> Int =
    match expr with
    | Int i -> i
    | Binop l op r ->
        let f =
            // Operators are just functions and can be referred to like any other identifier
            // by wrapping them in parentheses
            match op with
            | Add -> (+)
            | Sub -> (-)
            | Div -> (/)
            | Mul -> (*)
        f (eval l) (eval r)

do digits =
    let gen_digit = random.thread_rng.gen_int_range 1 10
    do a = gen_digit
    do b = gen_digit
    do c = gen_digit
    do d = gen_digit
    wrap [a, b, c, d]

let print_digits = for digits (\d ->
        seq io.print " "
        io.print (show d))
seq io.print "Four digits:" *> print_digits *> io.println ""

let guess_loop _ =
    do line = io.read_line
    // Exit the program if the line is just whitespace
    if string.is_empty (string.trim line) then
        wrap ()
    else
        match parse line with
        | Err err -> io.println err *> guess_loop ()
        | Ok expr ->
            if validate digits expr then
                let result = eval expr
                if result == 24
                then io.println "Correct!"
                else io.println ("Incorrect, " <> int.show.show result <> " != 24") *> guess_loop ()
            else
                io.println
                    "Expression is not valid, you must use each of the four numbers exactly once!"
                    *> guess_loop ()

guess_loop ()
```

[Source][24 game]

## Getting started

### Try online

You can try gluon in your browser at https://gluon-lang.org/try/. ([Github](https://github.com/gluon-lang/try_gluon))

### Install

Gluon can be installed by using one of the prebuilt executables at [Github](https://github.com/gluon-lang/gluon/releases) or you can use Cargo in order to install the `gluon_repl` crate:

```
cargo install gluon_repl
```

### REPL

Gluon has a small executable that can be used to run gluon programs directly or in a small REPL. The REPL can be started by passing the `-i` flag to the built repl executable which can be run with `cargo run -p gluon_repl -- -i`.

REPL features:
* Evaluating expressions (expressions of type IO will be evaluated in the IO context).
* Bind variables by writing `let <pattern> <identifier>* = <expr>` (omitting `in <expr>` from a normal let binding)
    Example:

         let f x = x + 1
         let { x, y = z } = { x = 1, y = 2 }
         f z

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

## Tools

### Language server

Gluon has a [language server](https://github.com/gluon-lang/gluon_language-server) which provides code completion and formatting support. Installation is done with `cargo install gluon_language-server`.

### Visual Studio Code Extension

The [gluon extension][] for Visual Studio Code provides syntax highlighting and completion. To install it, search for `gluon` among the extensions. ([Github](https://github.com/gluon-lang/gluon_language-server)) 

![example](http://i.imgur.com/44bH0ww.gif)

[gluon extension]:https://marketplace.visualstudio.com/items?itemName=Marwes.gluon

### Vim plugin

[vim-gluon](https://github.com/gluon-lang/vim-gluon) provides syntax highlighting and indentation.

The gluon language server has been tested to work with https://github.com/autozimu/LanguageClient-neovim and https://github.com/prabirshrestha/vim-lsp. 

#### Example configuration (autozimu/LanguageClient-neovim)
```vim
let g:LanguageClient_serverCommands = {
    \ 'gluon': ['gluon_language-server'],
    \ }

" Automatically start language servers.
let g:LanguageClient_autoStart = 1

nnoremap <silent> K :call LanguageClient_textDocument_hover()<CR>
nnoremap <silent> gd :call LanguageClient_textDocument_definition()<CR>
```

## Documentation

[The Gluon Book](https://gluon-lang.org/doc/crates_io/book/index.html)

[Gluon Standard Library API Reference](https://gluon-lang.org/doc/crates_io/std/std.html)

[Rust API Docs](https://docs.rs/gluon/*/gluon/index.html)


## Usage

### Rust

Gluon requires a recent Rust compiler to build (1.9.0 or later) and is available at [crates.io](https://crates.io/crates/gluon). It can easily be included in a Cargo project by adding the lines below.

```toml
[dependencies]
gluon = "0.17.2"
```

### Other languages
Currently, the easiest way to interact with the gluon virtual machine is through Rust but a rudimentary [C api][] exists which will be extended in the future to bring it closer to the Rust API.

[C api]: https://github.com/gluon-lang/gluon/blob/master/c-api/src/lib.rs

## Contributing

There are many ways to contribute to gluon. The two simplest ways are opening issues or working on issues marked as [beginner][]. For more extensive information about contributing, you can look at [CONTRIBUTING.md][]. Contributing also has details on **running/getting-started-with tests** for gluon.

[beginner]:https://github.com/gluon-lang/gluon/labels/Beginner
[CONTRIBUTING.md]:https://github.com/gluon-lang/gluon/blob/master/CONTRIBUTING.md

## Goals
These goals may change or be refined over time as I experiment with what is possible with the language.

* **Embeddable** - Similiar to [Lua][Lua] - it is meant to be included in another program that may use the virtual machine to extend its own functionality.

* **Statically typed** - The language uses a [Hindley-Milner based type system][hm] with some extensions, allowing simple and general type inference.

* **Tiny** - By being tiny, the language is easy to learn and has a small implementation footprint.

* **Strict** - Strict languages are usually easier to reason about, especially considering that it is what most people are accustomed to. For cases where laziness is desired, an explicit type is provided.

* **Modular** - The library is split into its parser, type checker, and virtual machine + compiler. Each of these components can be used independently of each other, allowing applications to pick and choose exactly what they need.

[hm]:https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
[prelude]:https://github.com/gluon-lang/gluon/blob/master/std/prelude.glu

## Inspiration

This language takes its primary inspiration from [Lua][Lua], [Haskell][Haskell] and [OCaml][OCaml].

[Lua]: http://www.lua.org
[Haskell]: http://www.haskell.org
[OCaml]: http://www.ocaml.org
[Rust]: http://www.rust-lang.org
