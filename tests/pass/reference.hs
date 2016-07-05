let { run, monad, assert, assert_ieq, assert_feq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let { Num, Eq } = prelude
let { (==) } = prelude.eq_Int
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad

let ri = ref 0
assert (0 == load ri)
ri <- 2
assert (2 == load ri)
assert (2 == load ri)
ri <- 10
assert (10 == load ri)
True
