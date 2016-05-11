let prelude = import "std/prelude.hs"
let map = import "std/map.hs"
let string = import "std/string.hs"
let { Map } = map
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ } = prelude.make_Monad prelude.monad_IO
let { Eq, Option, Result, Monoid } = prelude
let { (==) } = string.eq
let (++) = string.monoid.(<>)
let { singleton, find, insert, monoid, to_list }
    = map.make string.ord
let { (<>), empty } = monoid


let load_file filename: String -> IO String =
    let last_slash =
        match string.rfind filename "/" with
            | None -> 0
            | Some i -> i + 1
    let modulename = string.slice filename last_slash (string.length filename - 3)
    let read_result = io.catch (io.read_file filename >>= \x -> return (Ok x)) (\err -> return (Err err))
    read_result >>= \result ->
        match result with
            | Ok expr -> io.load_script modulename expr
            | Err msg -> return msg

type Cmd = { info: String, action: String -> IO Bool }

let commands: Map String Cmd
    =  singleton "q" { info = "Quit the REPL", action = \_ -> return False }
        <> singleton "t" {
            info = "Prints the type with an expression",
            action = \arg -> repl_prim.type_of_expr arg >>= \result ->
                match result with
                | Ok x -> io.print x
                | Err x -> io.print x
                    >> return True
        }
        <> singleton "i" {
            info = "Prints information about the given name",
            action = \arg -> repl_prim.find_info arg >>= \result ->
                match result with
                | Ok x -> io.print x
                | Err x -> io.print x
                    >> return True
        }
        <> singleton "k" {
            info = "Prints the kind with the given type",
            action = \arg -> repl_prim.find_kind arg >>= \result ->
                match result with
                | Ok x -> io.print x
                | Err x -> io.print x
                    >> return True
        }
        <> singleton "l" {
            info = "Loads the file at 'folder/module.ext' and stores it at 'module'",
            action = \arg -> load_file arg >>= io.print >> return True
        }

let help =
    let info = "Print this help"
    {
        info,
        action = \_ ->
            io.print "Available commands\n" >>
                io.print ("    :h " ++ info) >>
                forM_ (to_list commands) (\cmd ->
                    //FIXME This type declaration should not be needed
                    let cmd: { key: String, value: Cmd } = cmd
                    io.print ("    :" ++ cmd.key ++ " " ++ cmd.value.info)
                ) >>
                return True
    }

let commands = insert "h" help commands
let do_command line: String -> IO Bool = 
    let cmd = string.slice line 1 2
    let arg = string.trim (string.slice line 3 (string.length line))
    match find cmd commands with
        | Some command -> command.action arg
        | None -> io.print ("Unknown command '"  ++ cmd ++ "'") >> return True

let store line: String -> IO Bool =
    let line = string.trim line
    match string.find line " " with
        | Some bind_end -> 
            let binding = string.slice line 0 bind_end
            let expr = string.slice line bind_end (string.length line)
            io.load_script binding expr >> return True
        | None -> io.print "Expected binding in definition" >> return True

let loop x: () -> IO () = io.read_line >>= \line ->
    (if string.starts_with line ":" then
        do_command line
    else if string.starts_with line "def " then
        store (string.slice line 4 (string.length line))
    else
        io.catch (io.run_expr line) return >>= io.print >> return True) >>= \continue -> 
            if continue then
                loop ()
            else
                return ()

loop
