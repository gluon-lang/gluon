let prelude = import "std/prelude.glu"
let { Writer } = import "std/writer.glu"
let { Test, run, monad, assert, assert_ieq, assert_feq } = import "std/test.glu"
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad

let tests =
    assert_ieq 1 1 >>
        assert_ieq 1 2 >>
        assert_ieq 1 1 >>
        assert_feq 1.0 10.0

assert (prelude.foldl (\acc _ -> 1 + acc) 0 tests.writer == 2)
