let { Monad, Monoid } = import "std/prelude.hs"
in
type Writer w a = { value: a, writer: w }
in
let make w: Monoid w -> Monad (Writer w) = {
    (>>=) = \m g ->
        let { value, writer } = g m.value
        in { value, writer = w.(<>) m.writer writer },
    return = \value -> { value, writer = w.empty }
}
in
let tell w: w -> Writer w () =
    { value = (), writer = w }
in
{ Writer, make, tell }
