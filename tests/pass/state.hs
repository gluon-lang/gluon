let { Monad, Num } = prelude
and { Writer } = import "std/writer.hs"
and { run, monad = monad_Test, assert, assert_ieq, assert_feq, assert_seq } = import "std/test.hs"
and { State, monad = monad_State, put, get, modify, runState, evalState, execState } = import "std/state.hs"
and { (>>) = (>>>) } = prelude.make_Monad monad_Test
and { (>>=), return, (>>) } = prelude.make_Monad monad_State
and { (+), (-), (*) } = prelude.num_Int
in
let tests =
        assert_ieq (execState (modify (\x -> x + 2) >> modify (\x -> x * 4)) 0) 8
        >>>
        assert_ieq (evalState (modify (\x -> x + 2) >> get) 0) 2
        >>>
        assert_seq (evalState (put "hello" >> get) "") "hello"
        >>>
        assert_seq (runState (put "hello" >> get) "").value "hello"
in
run tests
