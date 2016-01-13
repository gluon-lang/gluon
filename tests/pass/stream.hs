let prelude = import "std/prelude.hs"
and { run, monad, assert_eq, assert_ieq } = import "std/test.hs"
and stream = import "std/stream.hs"
in
let { Ord, Num, List, Option } = prelude
in
let { (<) } = prelude.make_Ord prelude.ord_Int
in
let { (+) } = prelude.num_Int
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
in
let s = stream.from (\i -> if i < 5 then Some i else None)
and assert_leq = assert_eq (prelude.show_List prelude.show_Int) (prelude.eq_List prelude.eq_Int)
in
assert_ieq (stream.fold (+) 0 s) 10 >> 
assert_leq (stream.fold (\h l -> Cons h l) Nil s) (Cons 4 (Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil)))))
