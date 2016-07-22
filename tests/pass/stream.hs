let prelude = import "std/prelude.glu"
let { run, applicative, monad, assert_eq, assert_ieq } = import "std/test.glu"
let stream = import "std/stream.glu"
let { Ord, Num, List, Option } = prelude
let { (<) } = prelude.make_Ord prelude.ord_Int
let { (+) } = prelude.num_Int
let { (>>) } = prelude.make_Monad monad applicative

let s = stream.from (\i -> if i < 5 then Some i else None)

let assert_leq = assert_eq (prelude.show_List prelude.show_Int) (prelude.eq_List prelude.eq_Int)

assert_ieq (stream.fold (+) 0 s) 10 >>
    assert_leq (stream.fold (\h l -> Cons h l) Nil s) (Cons 4 (Cons 3 (Cons 2 (Cons 1 (Cons 0 Nil)))))
