let { run, writer, assert_eq } = import "std/test.glu"
let prelude = import "std/prelude.glu"
let { (*>) } = prelude.make_Applicative writer.applicative

let test_alt show eq alt =
    let { (<|>), or, empty, many, some } = prelude.make_Alternative alt
    let { pure } = alt.applicative

    let assert =
            assert_eq (show prelude.show_Int) (eq prelude.eq_Int)

    assert empty empty
        *> assert (empty <|> pure 1) (pure 1)
        *> assert (empty <|> empty) empty
        *> assert (empty <|> empty <|> pure 10) (pure 10)

test_alt prelude.show_Option prelude.eq_Option prelude.alternative_Option
    *> test_alt prelude.show_List prelude.eq_List prelude.alternative_List
