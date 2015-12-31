let { Writer } = import "std/writer.hs"
in
let { run, monad, assert, assert_ieq, assert_feq } = import "std/test.hs"
in
let { Eq, Num, List, (++) } = prelude
in
let { (+) } = prelude.num_Int
in
let { (==) } = prelude.eq_Int
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
in
let tests =
    assert_ieq 1 1 >>
    assert_ieq 1 2 >>
    assert_ieq 1 1 >>
    assert_feq 1.0 10.0
in
assert (prelude.foldl (\acc _ -> 1 + acc) 0 tests.writer == 2)
