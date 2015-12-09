let { Monad } = prelude
in
type State s a = s -> { value: a, state: s }
in
let (>>=) m f: State s a -> (a -> State s b) -> State s b =
    \state ->
        let { value, state } = m state
        and m2 = f value
        in m2 state
in
let return value: a -> State s a = \state -> { value, state }
in
let monad_State: Monad (State s) = { (>>=), return }
in
let put value: s -> State s () = \state -> { value = (), state = value }
in
let get: State s s = \state -> { value = state, state }
in
let gets f: (s -> a) -> State s a = \state -> { value = f state, state }
in
let modify f: (s -> s) -> State s () = \state -> { value = (), state = f state }
in
let runState f state: State s a -> s -> { value: a, state: a } = f state
in
let evalState f state: State s a -> s -> a = (runState f state).value
in
let execState f state: State s a -> s -> s = (runState f state).state
in { monad_State, put, get, modify, runState, evalState, execState }
