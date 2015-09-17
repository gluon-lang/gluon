let (++) = string.append
and { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
    = prelude.make_Monad prelude.monad_IO
in
let assert x = if x then return () else error "Assertion failed"
and assert_eq show eq = \x y ->
    if eq.(==) x y
    then return ()
    else error ("Assertion failed: "
                ++ show.show x  ++ " != " ++ show.show y)
in
let assert_ieq = assert_eq prelude.show_Int prelude.eq_Int
in
let { (+), (-), (*) } = prelude.num_Int in
    let l = lazy (\_ -> 123 + 57) in
    assert_ieq (force (lazy \_ -> 2)) 2 >>
    return () >> assert_ieq 180 (force l)
