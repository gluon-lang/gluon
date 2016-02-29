let prelude = import "std/prelude.hs"
and { Ordering, Ord, Option, List, Monoid } = prelude
in
type Map k a = | Bin k a (Map k a) (Map k a)
               | Tip
in let empty = Tip
in
let singleton k v = Bin k v empty empty
and make ord =
    let compare = ord.compare
    in
    let find k m =
        case m of
            | Bin k2 v l r ->
                (case compare k k2 of
                    | LT -> find k l
                    | EQ -> Some v
                    | GT -> find k r)
            | Tip -> None
    and insert k v m =
        case m of
            | Bin k2 v2 l r ->
                case compare k k2 of
                    | LT -> Bin k2 v2 (insert k v l) r
                    | EQ -> Bin k v l r
                    | GT -> Bin k2 v2 l (insert k v r)
            | Tip -> Bin k v empty empty
    and to_list m =
        let (++) = prelude.monoid_List.(<>)
        case m of
            | Bin key value l r -> to_list l ++ Cons { key, value } (to_list r)
            | Tip -> Nil
    in
    let (<>) l r =
        case l of
            | Bin lk lv ll lr ->
                case r of
                    | Bin rk rv rl rr ->
                        case compare lk rk of
                            | LT -> Bin lk lv ll (lr <> r)
                            | EQ -> Bin lk lv (ll <> rl) (lr <> rr)
                            | GT -> Bin lk lv (ll <> r) lr
                    | Tip -> l
        | Tip ->
            case r of
                | Bin a b c d -> r
                | Tip -> empty
    in
    let monoid = { (<>), empty }
    in { monoid, singleton, find, insert, to_list }
in { Map, make }
