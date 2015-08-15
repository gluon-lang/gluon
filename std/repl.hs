let { (>>=), return } = prelude.monad_IO
and (>>) = \l r -> l >>= \_ -> r
and { (==) } = prelude.eq_String
and (++) = string_append
in
let load_file filename: String -> IO String =
    let last_slash = (\_ -> case string_rfind filename "/" of
        | None -> 0
        | Some i -> i #Int+ 1) ()
    and modulename = string_slice filename last_slash (string_length filename #Int- 3)
    and read_result = catch_IO (read_file filename >>= \x -> return (Ok x)) (\err -> return (Err err))
    in read_result >>= \result ->
        case result of
            | Ok expr -> load_script modulename expr
            | Err msg -> return msg
in
let do_command line: String -> IO Bool
    = 
    let cmd = string_slice line 1 2
    and arg = string_trim (string_slice line 3 (string_length line))
    in if cmd == "q"
        then return False
        else if cmd == "t"
        then type_of_expr arg >>= print >> return True
        else if cmd == "i"
        then find_type_info arg >>= print >> return True
        else if cmd == "l"
        then load_file arg >>= print >> return True
        else print (string_append "Unknown command " cmd) >> return True
in
let loop x: () -> IO () = read_line >>= \line ->
    let is_command = string_slice line 0 1 == ":"
    in (if is_command
        then do_command line
        else run_expr line >>= print >> return True) >>= \continue -> 
            if continue
            then loop ()
            else return ()
in loop ()
