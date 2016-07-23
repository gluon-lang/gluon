let { run, monad, assert, assert_ieq, assert_feq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let { Num } = prelude
let { (>>) } = prelude.make_Monad monad

let int_tests =
    let { (+), (-), (*) } = prelude.num_Int
    assert_ieq 2 2 >>
        assert_ieq 12 (10 + 2) >>
        assert_ieq 123 (50 * 2 + 9 * 3 - 4)

let float_tests =
    let { (+), (-), (*) } = prelude.num_Float
    assert_feq 91.0 (50.0 * 2.0 - 3.0 * 3.0)

int_tests >> float_tests
