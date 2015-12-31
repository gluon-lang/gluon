let string = import "std/string.hs"
and writer = import "std/writer.hs"
and { Show, Num, Eq, Option, List, Monad } = prelude
and { (+) } = prelude.num_Int
and { (==) } = prelude.eq_Int
and { (<) } = prelude.make_Ord prelude.ord_Int
in
let (++) = string.append
in
let { Writer, make, tell } = writer
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
    = prelude.make_Monad (make Nil (prelude.(++)))
in
let assert x = if x then () else error "Assertion failed"
and assert_eq show eq = \x y ->
    if eq.(==) x y
    then return ()
    else tell (Cons ("Assertion failed: "
                ++ show.show x  ++ " != " ++ show.show y) Nil)
in
let assert_ieq = assert_eq prelude.show_Int prelude.eq_Int
and assert_feq = assert_eq prelude.show_Float prelude.eq_Float
in
let writer =
    assert_ieq 1 1 >>
    assert_ieq 1 2 >>
    assert_ieq 1 1 >>
    assert_feq 1.0 10.0
in
assert (prelude.foldl (\acc _ -> 1 + acc) 0 writer.writer == 2)
