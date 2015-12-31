let { Option, Num } = prelude
and { (+) } = prelude.num_Int
in
type Stream a =
    | LazyStream (Lazy (Stream a))
    | Value a (Stream a)
    | Empty
in
let from f: (Int -> Option a) -> Stream a =
        let from_ i =
                LazyStream (lazy (\_ -> case f i of
                    | Some x -> Value x (from_ (i + 1))
                    | None -> Empty
                ))
        in from_ 0
in
let next stream: Stream a -> { value: Option a, rest: Stream a } =
    case stream of
        | LazyStream l -> next (force l)
        | Value x xs -> { value = Some x, rest = xs }
        | Empty -> { value = None, rest = Empty }
in
let fold f b stream: (a -> b -> b) -> b -> Stream a -> b =
    let { value, rest } = next stream
    in
    case value of
        | Some a -> fold f (f a b) rest
        | None -> b
in
{ from, next, fold }
