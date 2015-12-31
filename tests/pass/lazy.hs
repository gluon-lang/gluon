let { run, monad, assert_ieq } = import "std/test.hs"
in
let { Num } = prelude
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
in
let { (+), (-), (*) } = prelude.num_Int in
    let l = lazy (\_ -> 123 + 57) in
    assert_ieq (force (lazy \_ -> 2)) 2 >>
    return () >> assert_ieq 180 (force l)
