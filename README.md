# embed_lang (working title)

This library is a complete compiler and virtual machine for an embeddable langauge implemented in pure [Rust][Rust]. This is currently very unstable as neither the semantics of syntax is nailed down yet.

## Usage

### REPL
There is a rudimentary REPL which can be used by passing the `-i` flag to the built executable (after running cargo build, run `target/debug/repl -i`). The REPL is currently capable of:
* Evaluating expressions (expressions of type IO will be evaluated in the IO context).
* Loading files with `:l path_to_file` the result of evaluating the expression in the loaded file is stored in a variable named after the filename without an extension.
* Checking the types of expressions with `:t expression`
* Checking type information with `:i type`
* Exiting the REPL by writing `:q`

As a warning, the standard math operators (+, -, * etc) are not exported in the global scope, as such the expression `2 + 2` will not compile. To use these operators they need to explicitly be brought into scope `let { (+), (-), (*) } = prelude.num_Int in 2 + 2`. See the reason for this in issue [#10][]

## Goals/Features
These goals may change or be refined over time as I experiment with what is possible to with the language.

* **Statically typed** - It currently uses the Hindley-Milner type system with some extensions.

* **Tiny** - The language should be as small as possible while still remaining practical. As having a static typesystem already demands a good chunk of extra code it becomes even more important to have a very small set of features as every feature added is likely to need code added to the parser, typechecker as well as the compiler causing even small additions to add a larger amount of code than it would in a dynamic language.

  As an example, there is no concept of modules as a concept of grouping code. Instead the basic records fills the same role (Caveat: Types currently always globally exported though this should change). Now instead of files being compiled as modules they are just expressions which return a record of the functions they export! See the [prelude][] for an example.

* **Strict** - Laziness is supported through an explicit type but being strict by default leads to easier to debug code.

* **Modular** - The library is split into parser, typechecker and virtual machine + compiler currently and these parts should for the most part be possible to be used independently. Certain language agonstic things are also likely candidates for separation from the main library. For instance the garbage collector is currently quite unaware of the rest of the code and might be made into separate crate (if you see something useful separately from the library please don't hesitate to open an issue!).

* **Embeddable** - Similiar to [Lua][Lua] it is meant to be able to be included in another program which can use the virtual machine to extend its own functionality.

* **Pure** The language is currently pure but this could likely change as the goal to be embeddable means that it will interact with non-pure languages leading purity to be to restrictive.

[#10]:https://github.com/Marwes/embed_lang/issues/10
[prelude]:https://github.com/Marwes/embed_lang/blob/master/std/prelude.hs

## Inspiration

This language takes its primary inspiration from [Lua][Lua], [Haskell][Haskell] and [OCaml][OCaml].

[Lua]: http://www.lua.org
[Haskell]: http://www.haskell.org
[OCaml]: http://www.ocaml.org
[Rust]: http://www.rust-lang.org
