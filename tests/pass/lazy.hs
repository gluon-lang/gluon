let { run, monad, assert_ieq } = import "std/test.hs"
let prelude = import "std/prelude.hs"
let { Num } = prelude
let { (>>=), return, (>>), join, map, lift2, forM_ }
        = prelude.make_Monad monad
let { (+), (-), (*) } = prelude.num_Int

let l = lazy (\_ -> 123 + 57)

assert_ieq (force (lazy \_ -> 2)) 2 >>
    return () >>
    assert_ieq 180 (force l)
