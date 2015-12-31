let string = import "std/string.hs"
and stream = import "std/stream.hs"
and { Show, Num, Eq, Option, List } = prelude
and { (+) } = prelude.num_Int
and { (<) } = prelude.make_Ord prelude.ord_Int
in
let (++) = string.append
and { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
    = prelude.make_Monad prelude.monad_IO
in
let assert x = if x then return () else error "Assertion failed"
and assert_eq show eq = \x y ->
    if eq.(==) x y
    then return ()
    else error ("Assertion failed: "
                ++ show.show x  ++ " != " ++ show.show y)
in
let assert_ieq = assert_eq prelude.show_Int prelude.eq_Int
and assert_leq = assert_eq (prelude.show_List prelude.show_Int) (prelude.eq_List prelude.eq_Int)
in
let s = stream.from (\i -> if i < 5 then Some i else None)
in
assert_ieq (stream.fold (+) 0 s) 10 >> 
assert_leq (stream.fold (\h l -> Cons h l) Nil s) (Cons 4 (Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil)))))
