# Anatomy of a gluon program

Let's look at a slightly larger program by writing a guessing game. In this game the player will guess at a random number between 1 and 100 and the program will say whether each guess is too low or too high. If the player guesses correctly the program will congratulate the player and exit.

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

`do expressions` are similar to `let expressions` in that they let us bind the result of an expression to a name which we can use later. Where they differ is that, rather binding the result of evaluating the expression itself, they expect the right hand side to be a monadic action such as `IO` and the value bound is the result of evaluating the action, which in this case is the `String` that were input.

(As was alluded to in the previous paragraph `IO` is a `Monad`, a rather complex concept which I won't go into here as it is enough for our purposes to only consider the "IO monad" as something that describes how `IO` actions are run in sequence.)

`do expressions` don't just magically work with `IO` actions which is where `implicit arguments` come in, it lets us use the compiler to implicitly insert certain function arguments by looking at the inferred types. This can be thought as a way to get something similar to `traits` in Rust but with a bit extra flexibility by requiring a bit of explicitness to let the compiler know what it can use as an implicit argument. Which is why we needed to add the `{ ? }` record pattern match, the `?` lets the compiler know that it should choose from the fields of the record when looking for an implicit argument.  In this case the compiler sees that we use `IO` in the `do expression` and implicitly inserts an implicit [`Monad IO`][] value found in `std.io`, letting the `do expression` know how to sequence these two actions.

[`Monad IO`]:https://gluon-lang.org/doc/nightly/std/io.html#value.monad

Next we will need to generate a number for the player to guess. For this we will use the [`std.random`][] module and specifically the [`thread_rng.gen_int_range`][] `IO` action. So we will need to run it using `do` again. Lets also output the number so that to see how it works, since `io.println` takes a `String` we will need to convert the number before outputting it which we can do with [`show`][].

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random

do target_number = random.thread_rng.gen_int_range 1 101

do line = io.read_line
io.println (show target_number)
```

The program should now output a random number between 1 and 100 on every run! We aren't checking if that number matches the input from the user yet however so lets do that next.

To check that the input is actually a number and retrieve it as such we can use the [`std.int.parse`][] function. We also need to trim whitespace from the line we read as it contains a trailing newline.

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result

do _ = io.println "Guess a number between 1 and 100!"
do target_number = random.thread_rng.gen_int_range 1 101

do line = io.read_line
match int.parse (string.trim line) with
| Err _ ->
    io.println "That is not a number!"
| Ok guess ->
    if guess == target_number then
        io.println "Correct!"
    else
        io.println "Wrong!"
```

If you try and run the program now it should only let you input numbers and give you a chance at the correct number. As it is you only got the one chance now though so lets make it possible to try again if the guess is wrong!

To implement repetition we will need to write a function, specifically a recursive function. As long as the guess is wrong we just say that the guess was wrong and then repeat the process by having the function call itself, if the guess was correct then we exit the program.

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result

do _ = io.println "Guess a number between 1 and 100!"
do target_number = random.thread_rng.gen_int_range 1 101

let guess_number _ : () -> IO () =
    do line = io.read_line
    match int.parse (string.trim line) with
    | Err _ ->
        do _ = io.println "That is not a number!"
        guess_number ()
    | Ok guess ->
        if guess == target_number then
            io.println "Correct!"
        else
            do _ = io.println "Wrong!"
            guess_number ()

// Start the first guess
guess_number ()
```

Now there is at least a way to guess again on the same number! It is still a rather tedious game though as the only hint we get is that the number is between 1 and 100 so lets add the last part of letting the program tell whether the guess is too high or too low. 

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result
let { Ordering, compare } = import! std.cmp

do _ = io.println "Guess a number between 1 and 100!"
do target_number = random.thread_rng.gen_int_range 1 101

let guess_number _ : () -> IO () =
    do line = io.read_line
    match int.parse (string.trim line) with
    | Err _ ->
        do _ = io.println "That is not a number!"
        guess_number ()
    | Ok guess ->
        match compare guess target_number with
        | EQ -> io.println "Correct!"
        | LT ->
            do _ = io.println "Wrong! Your guess is too low!"
            guess_number ()
        | GT ->
            do _ = io.println "Wrong! Your guess is too high!"
            guess_number ()

// Start the first guess
guess_number ()
```

And there we have it, the final program! There are ways to improve this but lets leave that for the next chapter.

[`std.random`]:https://gluon-lang.org/doc/nightly/std/random.html
[`thread_rng.gen_int_range`]:https://gluon-lang.org/doc/nightly/std/random.html#value.thread_rng
[`std.show`]:https://gluon-lang.org/doc/nightly/std/show.html#value.show
[`std.int.parse`]:https://gluon-lang.org/doc/nightly/std/int.html#value.parse
