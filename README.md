# embed_lang (working title)

This library is a complete compiler and virtual machine for implemented in [Rust][Rust].
## Usage

You can start a rudimentary REPL by starting the repl binary using -i. It currently has support for:
* Evaluating expressions (expressions of type IO will be evaluated in the IO context).
* Loading files with `:l filename` the result of evaluating the expression in `filename` is store in a variable called `filename` without the extension.
* Checking the types of expressions with `:t expression`

## Goals/Features
These goals may change or be refined over time as I experiment with what is possible to with the language.

* **Statically typed** - It currently roughly uses the Hindley-Milner type system with some extensions.

* **Tiny** - The language should be as small as possible while still remaining practical. Every feature added should be turned on its head several time and asked "Can I do this with what already exists". An example of this is that previously there was a difference between compiling a module, which was a list of bindings and types, and an expression. Modules where removed as practically the same result could be achieved by returning a record of the bindings (Caveat: Types currently always globally exported though this should change). Now instead of files being compiled as modules they are just expressions which return a record of the functions they export!

* **Strict** - Laziness will probably be supported through an explicit type but being strict by default leads to easier to debug code.

* **Pure** Purity is a really powerful concept when reasoning about code. The language is currently pure though given the goal to be embeddable this might be to restrictive.

* **Modular** - The entire library will be split into multiple crates over time allowing the virtual machine, compiler, typechecker and parser to be used separately. Certain language agonstic things are also likely for separation from the main library. For instance the garbage collector is currently quite unaware of the rest of the code and might be made into separate crate (if you see something useful separately from the library please don't hesitate to open an issue).

* **Embeddable** - Similiar to [Lua][Lua] it is meant to be able to be included in another program which can use the virtual machine to extend its own functionality.


## Inspiration

This language takes its primary inspiration from [Lua][Lua], [Haskell][Haskell] and [OCaml][OCaml].

[Lua]: www.lua.org
[Haskell]: www.haskell.org
[OCaml]: www.ocamlorg
[Rust]: www.rust-lang.org
