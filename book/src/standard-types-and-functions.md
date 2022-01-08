# Standard types and functions

The API documentation for the standard library can be found [here][std-docs]. Some of the modules
are only available if Gluon is compiled with the required features:

- `std.regex` requires the `regex` feature (enabled by default)
- `std.random` requires the `rand` feature (enabled by default)
- All `std.json.*` modules require the `serialization` feature

TODO

### Prelude

When compiling an expression, the compiler automatically inserts a small prelude before the expression itself, which gives automatic access to basic operators such as `+`, `-`, etc as well as types such as `Option` and `Result`.

### Threads and channels

Gluon has support for cooperative threading and communication between them through the `Thread` and `Sender`/`Receiver` types.

### Strings

`String` is a built-in data type. The module `std.string` provides the infix operatoin `++`, concatenating two strings. The operation `show` converts the Int to a printable String.
```
let io @ { ? } = import! std.io
let string @ { (++), len } = import! std.string
let { show }  = import! std.show
let message : String = "Hello" ++ " " ++ "World" ++ "!"
let prompt s = "<" ++   show (len s) ++ "> "
io.println ( (prompt message) ++ message )
```
The output will be
```
<12> Hello World!
```

The module `std.string` is providing the following operations
```
eq : std.cmp.Eq String,
ord : std.cmp.Ord String,
show : std.show.Show String,
semigroup : std.semigroup.Semigroup String,
monoid : std.monoid.Monoid String,
(++) : String -> String -> String,
len : String -> Int,
is_empty : String -> std.types.Bool,
is_char_boundary : String -> Int -> std.types.Bool,
as_bytes : String -> Array Byte,
split_at : String -> Int -> (String, String),
contains : String -> String -> std.types.Bool,
starts_with : String -> String -> std.types.Bool,
ends_with : String -> String -> std.types.Bool,
find : String -> String -> std.types.Option Int,
rfind : String -> String -> std.types.Option Int,
trim : String -> String,
trim_start : String -> String,
trim_start_matches : String -> String -> String,
trim_end : String -> String,
trim_end_matches : String -> String -> String,
append : String -> String -> String,
append_char : String -> Char -> String,
from_char : Char -> String,
slice : String -> Int -> Int -> String,
from_utf8 : Array Byte -> std.types.Result () String,
char_at : String -> Int -> Char
```

TODO

[std-docs]: http://gluon-lang.org/doc/nightly/std/index.html
