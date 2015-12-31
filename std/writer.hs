let { Monad } = prelude
in
type Writer w a = { value: a, writer: w }
in
let make w f: w -> (w -> w -> w) -> Monad (Writer w) = {
    (>>=) = \m g ->
        let { value, writer } = g m.value
        in { value, writer = f m.writer writer },
    return = \value -> { value, writer = w }
}
in
let tell w: w -> Writer w () =
    { value = (), writer = w }
in
{ Writer, make, tell }
