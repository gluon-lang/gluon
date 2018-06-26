# Using the REPL

Though it is possible to continue running any programs by saving it to a file and running it with `gluon my_script.glu` there is an easier way to go about it when you want to experiment quickly with small programs. By running `gluon -i`, gluon starts in "interactive" mode, giving you a REPL where you may evaluate expressions and inspect their results. Try evaluating some simple arithmetic expressions to see that it works.

```
> 1 + 2
3
> 100 * 3 + 4
304
> 3.14 * 10.0
31.400000000000002
```

Evaluating only a single expression can get quite unwieldy so if we want to break something up into multiple steps we can use `let` to give a name to an expression.

```
> let pi_2 = 3.14 * 2.0
6.28
> pi_2 * 3.0
18.84
```

These are the basic parts of the REPL and if you want to you can try writing hello world again by using the features above.

If you still have the `hello_world.glu` file around there is another way to run it from inside the REPL by using the special `:script` (`:s`) command.

```
> :s hello_world.glu
Hello World!
```

There are a few other of these special commands as well and you can find them all with `:help` (`:h`).


```
> :type 1
Int
> :info std.io.println
std.io.println: String -> IO ()
> :kind std.option.Option
Type -> Type
```

Finally you may quit the REPL using the `:quit` (`:q`) command or using `<CTRL-D>`.
