let prelude = import "std/prelude.glu"
let { Monad, Num } = prelude
let { Test, run, writer, assert, assert_ieq, assert_feq, assert_seq } = import "std/test.glu"
let state = import "std/state.glu"
let { State, put, get, modify, runState, evalState, execState } = import "std/state.glu"
let { (>>) = (>>>) } = prelude.make_Monad writer.monad
let { (>>) } = prelude.make_Monad state.monad
let { (+), (-), (*) } = prelude.num_Int

let tests =
    assert_ieq (execState (modify (\x -> x + 2) >> modify (\x -> x * 4)) 0) 8
        >>>
        assert_ieq (evalState (modify (\x -> x + 2) >> get) 0) 2
        >>>
        assert_seq (evalState (put "hello" >> get) "") "hello"
        >>>
        assert_seq (runState (put "hello" >> get) "").value "hello"

run tests
