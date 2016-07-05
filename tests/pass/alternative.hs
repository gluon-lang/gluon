let { run, monad, assert_eq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let { Applicative } = prelude
let { (>>=), return, (>>), join, map, lift2, forM_ }
        = prelude.make_Monad monad

let test_alt show eq fun alt app = 
    let { (<|>), empty, many, some } = prelude.make_Alternative fun app alt
    let { (<*>), pure } = app
    let assert =
            assert_eq (show prelude.show_Int) (eq prelude.eq_Int)

    assert empty empty >>
        assert (empty <|> pure 1) (pure 1) >>
        assert (empty <|> empty) empty >>
        assert (empty <|> empty <|> pure 10) (pure 10)

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
