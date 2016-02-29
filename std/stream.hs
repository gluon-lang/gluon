let prelude = import "std/prelude.hs"
and { Option, Num } = prelude
and { (+) } = prelude.num_Int
in
type Stream_ a =
    | Value a (Stream a)
    | Empty
and Stream a = Lazy (Stream_ a)
in
let from f: (Int -> Option a) -> Stream a =
        let from_ i =
                lazy (\_ ->
                    case f i of
                        | Some x -> Value x (from_ (i + 1))
                        | None -> Empty
                )
        in from_ 0
in
let next stream: Stream a -> Option a =
    case force stream of
        | Value x _ -> Some x
        | Empty -> None
and is_empty stream: Stream a -> Bool =
    case force stream of
        | Value _ _ -> False
        | Empty -> True
and fold f b stream: (a -> b -> b) -> b -> Stream a -> b =
    case force stream of
        | Value x xs -> fold f (f x b) xs
        | Empty -> b
in
{ from, next, is_empty, fold }
