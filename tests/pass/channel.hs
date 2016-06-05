let { run, monad, assert_eq } = import "std/test.hs"
let prelude = import "std/prelude.hs"
let { (>>=), return, (>>), join, map, lift2, forM_ }
        = prelude.make_Monad monad

let assert =
    assert_eq (prelude.show_Result prelude.show_Unit prelude.show_Int )
              (prelude.eq_Result prelude.eq_Unit prelude.eq_Int)

let { sender, receiver } = channel 0

send sender 0
send sender 1
send sender 2

let tests =
    assert (recv receiver) (Ok 0) >>
        assert (recv receiver) (Ok 1) >>
        assert (recv receiver) (Ok 2)

run tests
