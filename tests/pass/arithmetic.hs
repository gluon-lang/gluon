let { run, monad, assert, assert_ieq, assert_feq } = import "std/test.hs"
in
let { Num } = prelude
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
in
let int_tests =
    let { (+), (-), (*) } = prelude.num_Int in
    assert_ieq 2 2 >>
    assert_ieq 12 (10 + 2) >>
    assert_ieq 123 (50 * 2 + 9 * 3 - 4)
and float_tests =
    let { (+), (-), (*) } = prelude.num_Float in
    assert_feq 91.0 (50.0 * 2.0 - 3.0 * 3.0)
in int_tests >> float_tests
