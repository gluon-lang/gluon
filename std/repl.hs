let (>>=) = prelude.monad_IO.(>>=)
and (>>) = \l r -> l >>= \_ -> r
and return = prelude.monad_IO.return
and (==) = prelude.eq_String.(==)
in
let load_file line: String -> IO String =
    let filename = string_trim (string_slice line 3 (string_length line))
    and last_slash = (\_ -> case string_rfind filename "/" of
        | None -> 0
        | Some i -> i #Int+ 1) ()
    and modulename = string_slice filename last_slash (string_length filename #Int- 3)
    and read_result = catch_IO (read_file filename >>= \x -> return (Ok x)) (\err -> return (Err err))
    in read_result >>= \result ->
        case result of
            | Ok expr -> load_script modulename expr
            | Err msg -> return msg
in
let do_command cmd line: String -> String -> IO Bool
    = if cmd == ":q"
        then return False
        else if cmd == ":l"
        then load_file line >>= print >> return True
        else run_expr line >>= print >> return True
in
let loop x: () -> IO () = read_line >>= \line ->
    let
        cmd = string_slice line 0 2
    in do_command cmd line >>= \continue ->
        if continue
        then loop ()
        else return ()
in loop ()
