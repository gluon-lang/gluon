let string = import "std/string.hs"
and writer = import "std/writer.hs"
and { Writer, make, tell } = writer
and prelude = import "std/prelude.hs"
and { Show, Num, Eq, Option, List, Monad, Monoid, foldl } = prelude
and { (+) } = prelude.num_Int
and { (==) } = prelude.eq_Int
and { (<) } = prelude.make_Ord prelude.ord_Int
in
let (++) = string.monoid.(<>)
in
type Test a = Writer (List String) a
in
let monad: Monad Test = make prelude.monoid_List
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
in
let assert x = if x then () else error "Assertion failed"
and assert_eq show eq = \x y ->
    if eq.(==) x y
    then return ()
    else tell (Cons ("Assertion failed: "
                ++ show.show x  ++ " != " ++ show.show y) Nil)
in
let assert_ieq = assert_eq prelude.show_Int prelude.eq_Int
and assert_feq = assert_eq prelude.show_Float prelude.eq_Float
and assert_seq = assert_eq string.show string.eq
in
let run test: Test a -> () =
        match test.writer with
            | Cons _ _ -> error (prelude.foldl (\acc err -> acc ++ "\n" ++ err) "" test.writer)
            | Nil -> ()
in { Test, monad, assert, assert_eq, assert_ieq, assert_feq, assert_seq, run }
