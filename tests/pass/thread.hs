let { run, monad, assert_eq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let string = import "std/string.glu"
let { (>>=), (>>) } = prelude.make_Monad monad

let assert =
    assert_eq (prelude.show_Result prelude.show_Unit prelude.show_Int)
              (prelude.eq_Result prelude.eq_Unit prelude.eq_Int)
let assert_any_err =
    assert_eq (prelude.show_Result string.show prelude.show_Unit)
              (prelude.eq_Result { (==) = \x y -> True } prelude.eq_Unit)

let { sender, receiver } = channel 0

let thread = spawn (\_ ->
        send sender 0
        yield ()
        send sender 1
        yield ()
    )
resume thread

let tests =
    assert (recv receiver) (Ok 0) >>
        assert (recv receiver) (Err ()) >>= (\_ ->
            resume thread
            assert (recv receiver) (Ok 1)
        ) >>
        assert (recv receiver) (Err ()) >>= (\_ ->
            assert_any_err (resume thread) (Err "Any error message here")
        )

run tests
