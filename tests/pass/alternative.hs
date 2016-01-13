let { run, monad, assert_eq } = import "std/test.hs"
in
let prelude = import "std/prelude.hs"
and { Applicative } = prelude
in
let { (>>=), return, (>>), join, map = fmap, lift2, forM_ }
        = prelude.make_Monad monad
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
