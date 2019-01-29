# Extending the guessing game with effects

In the previous chapter we implemented a simple guessing game. In this chapter we will extend the final program with to keep track of how many guesses the player has done and finally report it at the end.

First, this was the final program from the previous chapter.

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

To keep track of how many guesses the player has done we need to keep some state as we go through each guess.
There are a few ways of doing this but the one we will look at here is using gluon's extensible effect system.
This can be found under the [`std.effect`][] module.

Extensible effects are a way to represent side effects in a composable way.
In other words, it is possible to use multiple different effects easily, something which can otherwise be fairly difficult with the monadic representation of side effects that gluon employs.

## Rewriting IO into Eff

Before we get into adding more effects though we first need to replace the `IO` monad with the [`Eff`][] monad used to represent effects.
Normally it is not possible to use a `Monad` directly when using effects and instead an entirely new "effect handler" needs to be written for the effect.
However, `Eff` allows the use of ONE `Monad` instance among the various effects in an effect row with the [`Lift`][] effect.

Lets see how we need to modify the code the guessing game to use `Eff` instead of `IO`, without adding any functionality.

[`std.effect`]:https://gluon-lang.org/doc/nightly/std/effect.html
[`Eff`]:https://gluon-lang.org/doc/nightly/std/effect.html#value.Eff
[`Lift`]:https://gluon-lang.org/doc/nightly/std/effect/lift.html#type.Lift

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result
let { Ordering, compare } = import! std.cmp

let { (<|) } = import! std.function
let effect @ { Eff, ? } = import! std.effect
let { Lift, run_lift, lift, ? } = import! std.effect.lift

let start _ : () -> Eff [| lift : Lift IO | r |] () =
    do _ = lift <| io.println "Guess a number between 1 and 100!"
    do target_number = lift <| random.thread_rng.gen_int_range 1 101

    let guess_number _ : () -> Eff [| lift : Lift IO | r |] () =
        do line = lift <| io.read_line
        match int.parse (string.trim line) with
        | Err _ ->
            do _ = lift <| io.println "That is not a number!"
            guess_number ()
        | Ok guess ->
            match compare guess target_number with
            | EQ -> lift <| io.println "Correct!"
            | LT ->
                do _ = lift <| io.println "Wrong! Your guess is too low!"
                guess_number ()
            | GT ->
                do _ = lift <| io.println "Wrong! Your guess is too high!"
                guess_number ()

    // Start the first guess
    guess_number ()

run_lift <| start ()
```

There is quite a bit going down here so lets break it down.

```f#,ignore
let { (<|) } = import! std.function
let effect @ { Eff, ? } = import! std.effect
let { Lift, run_lift, lift, ? } = import! std.effect.lift
```

Here we import a few new things. The first just imports the useful [`<|`][] operator, it doesn't really do any thing on its own and just serves as a way to let us avoid parentheses in a few places. Essentially `f <| a 123 "a"` is the same as `f (a 123 "a")`.

Next we import the [`Eff`][] type and its implicit instances so we can use `do` with it.

Finally we import [`Lift`][] and some functions to help us work with it. The `lift` function lets us "lift" a monadic action into the `Eff` monad. `run_lift` does the opposite, it takes the monadic action out of the `Eff` monad and lets us evaluate it.

[`<|`]:https://gluon-lang.org/doc/nightly/std/function.html#value.<|

```f#,ignore
let start _ : () -> Eff [| lift : Lift IO | r |] () =
```

Here we define our entrypoint and we can see the first use of the [`Eff`][] type and a new bit of syntax which describes an "effect row".

Effect rows are described in a similar manner to records, except they use `[|` and `|]` to delimit instead of `{` and `}`.
Rather than describing what fields a record holds they instead describe the effects used in this function.
In the same way as records, effect rows also has an optional `| r ` part which is what makes this "extensible" (see [polymorphic records][] in the reference).
If we defined the row without the `| r` part then we would get an error when trying to use the effect in a place that allows more effects.

[polymorphic records]:./syntax-and-semantics.html#polymorphic-records

```f#,ignore
let eff_closed : Eff [| eff_1 : Eff1 |] () = ...

let eff_open : Eff [| eff_1 : Eff1 | r |] () = ...

let eff : Eff [| eff_1 : Eff1, eff_2 : Eff2 | r |] () =
    // Error, type mismatch `[| eff_1 : Eff1 |]` does not contain `eff_2 : Eff2`
    do _ = eff_closed
    // Ok, because the action is polymorphic/extensible
    do _ = eff_open
    // etc
```

Essentially the type variable says that the effect "may have more effects then the ones specified" which lets us only specify the effects that each individual function needs while still being able to use them transparently in a program that uses additional effects.

In this place we only use the `lift : Lift IO` effect but we will see how we can use this to specify multiple effects in a little bit.

```f#,ignore
    do _ = lift <| io.println "Guess a number between 1 and 100!"
```

Here we actually start running an action. Since `io.println` returns an `IO ()` action and we need an `Eff [| lift : Lift IO | r |] ()` action we use `lift` to convert into the correct type. Otherwise the code is exactly the same as before!

(The need for `lift` is likely to be removed in the future.)

The lines that follow are all the same as before, only they may have received the `lift` treatment as well. Except for the last line.

```f#,ignore
run_lift <| start ()
```

Here we use [`run_lift`][] to go back from `Eff [| lift : Lift IO | r |] ()` into `IO ()` which the gluon interpreter can execute.

[`run_lift`]:https://gluon-lang.org/doc/nightly/std/effect/lift.html#value.run_lift

## Adding the State effect 

Now that we have the program written with [`Eff`][] we can use this to easily add some state to track how many guesses the player has done!

We do this using the [`State`][] effect which lets us hold a value in the `Eff` monad which we can read and write to.

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result
let { Ordering, compare } = import! std.cmp

let { (<|) } = import! std.function
let effect @ { Eff, ? } = import! std.effect
let { Lift, run_lift, lift, ? } = import! std.effect.lift
let { State, eval_state, ? } = import! std.effect.state

let start _ : () -> Eff [| lift : Lift IO, state : State Int | r |] () =
    do _ = lift <| io.println "Guess a number between 1 and 100!"
    do target_number = lift <| random.thread_rng.gen_int_range 1 101

    let guess_number _ : () -> Eff [| lift : Lift IO, state : State Int | r |] () =
        do line = lift <| io.read_line
        match int.parse (string.trim line) with
        | Err _ ->
            do _ = lift <| io.println "That is not a number!"
            guess_number ()
        | Ok guess ->
            match compare guess target_number with
            | EQ -> lift <| io.println "Correct!"
            | LT ->
                do _ = lift <| io.println "Wrong! Your guess is too low!"
                guess_number ()
            | GT ->
                do _ = lift <| io.println "Wrong! Your guess is too high!"
                guess_number ()

    // Start the first guess
    guess_number ()

run_lift <| eval_state 0 <| start ()
```

There are only two new things here, first we add `state : State Int` to the effect row to indicate that we want to use a state consisting of a single integer.

The second addition is to add `eval_state 0` before the `run_lift` call. This initializes the state with `0` and then evaluates the effect.

Notably we haven't actually used the state in any way except initializing it so lets actually use it. To work with the state we have the basic [`get`][], [`put`][] and [`modify`][] actions.'

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result } = import! std.result
let { Ordering, compare } = import! std.cmp

let { (<|) } = import! std.function
let effect @ { Eff, ? } = import! std.effect
let { Lift, run_lift, lift, ? } = import! std.effect.lift
let { State, eval_state, modify, get, ? } = import! std.effect.state

let start _ : () -> Eff [| lift : Lift IO, state : State Int | r |] () =
    do _ = lift <| io.println "Guess a number between 1 and 100!"
    do target_number = lift <| random.thread_rng.gen_int_range 1 101

    let guess_number _ : () -> Eff [| lift : Lift IO, state : State Int | r |] () =
        do line = lift <| io.read_line
        match int.parse (string.trim line) with
        | Err _ ->
            do _ = lift <| io.println "That is not a number!"
            guess_number ()
        | Ok guess ->
            // Increment the guess counter by one
            do _ = modify ((+) 1)
            match compare guess target_number with
            | EQ ->
                // Retrieve the guess so we can output it
                do guesses = get
                lift <| io.println ("Correct! You got it in " ++ show guesses ++ " guesses!")
            | LT ->
                do _ = lift <| io.println "Wrong! Your guess is too low!"
                guess_number ()
            | GT ->
                do _ = lift <| io.println "Wrong! Your guess is too high!"
                guess_number ()

    // Start the first guess
    guess_number ()

run_lift <| eval_state 0 <| start ()
```

We only needed to add two things here, first we add one on every guess using `modify` then we use `get` to retrieve the final amount when the player succeeded.


[`State`]:https://gluon-lang.org/doc/nightly/std/effect/state.html#type.State
[`get`]:https://gluon-lang.org/doc/nightly/std/effect/state.html#value.get
[`put`]:https://gluon-lang.org/doc/nightly/std/effect/state.html#value.put
[`modify`]:https://gluon-lang.org/doc/nightly/std/effect/state.html#value.modify

And that is all we had to do to add the guess tracking. The strength of extensible effects is precisely that there is very little work needed to add additional side effects to the program, despite the program as a whole still being entirely pure!

Just to show the strength of effects one last time we add the [`Error`][] effect to move the error handling outside of the main logic.

[`Error`]:https://gluon-lang.org/doc/nightly/std/effect/error.html#type.Error

```f#,rust
let io @ { ? } = import! std.io
let random = import! std.random
let int = import! std.int
let string = import! std.string
let { Result, map_err } = import! std.result
let { Ordering, compare } = import! std.cmp

let { (<|) } = import! std.function
let effect @ { Eff, ? } = import! std.effect
let { Lift, run_lift, lift, ? } = import! std.effect.lift
let { State, eval_state, modify, get, ? } = import! std.effect.state
let { Error, ok_or_throw, run_error, catch, ? } = import! std.effect.error


type GuessError =
    | NotANumber

let start _ : () -> Eff [| lift : Lift IO, state : State Int, error : Error GuessError | r |] () =
    do _ = lift <| io.println "Guess a number between 1 and 100!"
    do target_number = lift <| random.thread_rng.gen_int_range 1 101

    let guess_number _ : () -> Eff [| lift : Lift IO, state : State Int, error : Error GuessError | r |] () =
        do line = lift <| io.read_line
        do guess =
            ok_or_throw 
                <| map_err (\_ -> NotANumber)
                <| int.parse
                <| string.trim line
        do _ = modify ((+) 1)
        match compare guess target_number with
        | EQ ->
            do guesses = get
            lift <| io.println ("Correct! You got it in " ++ show guesses ++ " guesses!")
        | LT ->
            do _ = lift <| io.println "Wrong! Your guess is too low!"
            guess_number ()
        | GT ->
            do _ = lift <| io.println "Wrong! Your guess is too high!"
            guess_number ()

    // Start the first guess
    catch (guess_number ()) <| \err ->
        match err with
        | NotANumber -> 
            do _ = lift <| io.println "That is not a number!"
            guess_number ()

run_lift <| run_error <| eval_state 0 <| start ()
```
