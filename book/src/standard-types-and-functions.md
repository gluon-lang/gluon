# Standard types and functions

The API documentation for the standard library can be found [here][std-docs]. Some of the modules are only available if
Gluon is compiled with the required features:

- `std.regex` requires the `regex` feature (enabled by default)
- `std.random` requires the `rand` feature (enabled by default)
- All `std.json.*` modules require the `serialization` feature

TODO

### Prelude

When compiling an expression, the compiler automatically inserts a small prelude before the expression itself, which
gives automatic access to basic operators such as `+`, `-`, etc as well as types such as `Option` and `Result`.

### Threads and channels

Gluon has support for cooperative threading and communication between them through the `Thread` and `Sender`/`Receiver`
types.

### Strings

`String` is a built-in data type. The module `std.string` provides the infix operatoin `++`, concatenating two strings.
The operation `show` converts the Int to a printable String.

```
let io @ { ? } = import! std.io
let string @ { len } = import! std.string
let { show }  = import! std.show
let message : String = "Hello" ++ " " ++ "World" ++ "!"
let prompt s = "<" ++ show (len s) ++ "> "
io.println ( (prompt message) ++ message )
```

The output will be

```
<12> Hello World!
```

### Arrays

`Array` is a parameterized container of consecutive elements. The module `std.array` provides the following functions:

Creating arrays in gluon is easy with the array literal notation. It consists of two square brackets that wrap
optional array elements separated by a comma. Array elements can be any type Here are some examples
```
let a = [6, 2, 3]
show a
```
printing
```
"[6, 2, 3]"
```

`array.len` returns the length of the array

```
let a = [6, 2, 3]
let len = array.len a
len
```
printing
```
3
```

`array.slice` returns the slice of the array, specifying the index of first element and end index (behind last element)

```
let a = [6, 2, 3]
let start = 1
let non_inclusive_end = 3
let sl = array.slice a start non_inclusive_end
sl
```
printing 
```
[2, 3]
```

### Lists

`List` is a parameterized, linked list. The module  `std.list` provides the following functions:

The function `list.of` is used to create a list of an array.

```
let list @ { List, ? } = import! std.list
let a = [6, 2, 3]
list.of a
```
printing
```
Cons 6 (Cons 2 (Cons 3 Nil))
```

The function `map` applies a function to each element creating a new list.

```
let list @ { List, ? } = import! std.list
let { map } = import! std.functor
let a = [6, 2, 3]
let inc x : Int -> Int = x + 1
map inc (list.of a)
```
printing
```
Cons 7 (Cons 3 (Cons 4 Nil))
```

The following API doc for the module [`std.string`](https://gluon-lang.org/doc/crates_io/std/std/string.html) is a list
of all string operations.

```

TODO

[std-docs]: http://gluon-lang.org/doc/nightly/std/index.html
