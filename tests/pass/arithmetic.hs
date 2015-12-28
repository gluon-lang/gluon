let string = import "std/string.hs"
and { Show, Num, Eq } = prelude
in
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
and assert_feq = assert_eq prelude.show_Float prelude.eq_Float
and (++) = prelude.(++)
and int_tests =
    let { (+), (-), (*) } = prelude.num_Int in
    assert_ieq 2 2 >>
    assert_ieq 12 (10 + 2) >>
    assert_ieq 123 (50 * 2 + 9 * 3 - 4)
and float_tests =
    let { (+), (-), (*) } = prelude.num_Float in
    assert_feq 91.0 (50.0 * 2.0 - 3.0 * 3.0)
in int_tests >> float_tests
