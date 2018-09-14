# Anatomy of a gluon program (draft)

Let's look at a slightly larger program by writing a guessing game. In this game the player will guess at a random number between 1 and 100 and the program will say whether each guess is to low or to high. If the player guesses correctly the program will congratulate the player and exit.


As a base we can take the hello world example.

```f#,rust
let io = import! std.io
io.println "Hello world!"
```

The first thing we will need is a way to get a number from the user. For this we will use the `std.io.read_line : IO String` action. To test that it works we will simply write the line back to the user.

```f#,rust
let io @ { ? } = import! std.io
do line = io.read_line
io.println line
```

There are two new concepts in play here, [implicit arguments](./syntax-and-semantics.html#implicit-arguments) and [do expressions](./syntax-and-semantics.html#do-expressions).

`do expressions` are similar to `let expressions` in that they let us us bind the result of an expression to a name which we can use later. Where they differ is that, rather binding the result of evaluating the expression itself, they expect the right hand side to be a monadic action such as `IO` and the value bound is the result of evaluating the action, which in this case is the `String` that that were input.

(As was alluded to in the previous paragraph `IO` is a `Monad`, a rather complex concept which I won't go into here as it is enough for our purposes to only consider the "IO monad" as something that describes how `IO` actions are run in sequence.)

`do expressions` don't just magically work with `IO` actions which is where `implicit arguments` come in, it lets us use the compiler to to implicitly insert certain function arguments by looking at the inferred types. This can be thought as a way to get something similar to `traits` in Rust but with a bit extra flexibility by requiring a bit of explicitness to let the compiler know what it can use as an implicit argument. Which is why we needed to add the `{ ? }` record pattern match, the `?` lets the compiler know that it should choose from the fields of the record when looking for an implicit argument.  In this case the compiler sees that we use `IO` in the `do expression` and implicitly inserts an implicit `IO Monad` value found in `std.io`, letting the `do expression` know how to sequence these two actions.

