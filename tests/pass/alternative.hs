let string = import "std/string.hs"
and { Show, Num, Eq, Option, List, Functor, Applicative, Alternative } = prelude
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
let test_alt show eq fun alt app = 
    let { (<|>), empty, many, some } = prelude.make_Alternative fun app alt
    and { (<*>), pure } = app
    and assert =
            assert_eq (show prelude.show_Int) (eq prelude.eq_Int)
    in
    assert empty empty >>
    assert (empty <|> pure 1) (pure 1) >>
    assert (empty <|> empty) empty >>
    assert (empty <|> empty <|> pure 10) (pure 10)
in
test_alt
    prelude.show_Option
    prelude.eq_Option
    prelude.functor_Option
    prelude.alternative_Option
    prelude.applicative_Option
    >>
test_alt
    prelude.show_List
    prelude.eq_List
    prelude.functor_List
    prelude.alternative_List
    prelude.applicative_List
