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

TODO

[std-docs]: http://gluon-lang.org/doc/nightly/std/index.html
