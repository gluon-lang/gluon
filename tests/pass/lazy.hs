let { run, applicative, monad, assert_ieq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let { Num } = prelude
let { pure } = applicative
let { (>>) } = prelude.make_Monad monad applicative
let { (+), (-), (*) } = prelude.num_Int

let l = lazy (\_ -> 123 + 57)

assert_ieq (force (lazy \_ -> 2)) 2 >>
    pure () >>
    assert_ieq 180 (force l)
