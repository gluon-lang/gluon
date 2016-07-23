let prelude = import "std/prelude.glu"
let { Monad, Monoid, Option, List, Eq, Show } = prelude
let string = import "std/string.glu"
let { Test, run, writer, assert, assert_eq } = import "std/test.glu"
let map = import "std/map.glu"
let { (>>) } = prelude.make_Monad writer.monad

let show_Entry e =
    let { key, value } = e
    in string.monoid.(<>) key (prelude.show_Int.show value)
let eq_Entry l r: { key: String, value: Int } -> { key: String, value: Int } -> Bool =
        string.eq.(==) l.key r.key && prelude.eq_Int.(==) l.value r.value
let assert_list =
        assert_eq (prelude.show_List { show = show_Entry }) (prelude.eq_List { (==) = eq_Entry })
let assert_opt =
        assert_eq (prelude.show_Option prelude.show_Int) (prelude.eq_Option prelude.eq_Int)

let { singleton, find, insert, monoid, to_list } = map.make string.ord
let { (<>), empty } = monoid

let test_map = singleton "test" 1 <> singleton "asd" 2 <> singleton "a" 3
let tests =
        assert_opt (find "test" test_map) (Some 1)
            >>
            assert_opt (find "asd" test_map) (Some 2)
            >>
            assert_opt (find "b" test_map) None
            >>
            assert_opt (find "test" (insert "test" 10 test_map)) (Some 10)
            >>
            assert_opt (find "test" test_map) (Some 1)
            >>
            assert_list (to_list test_map) (Cons { key = "a", value = 3 }
                                           (Cons { key = "asd", value = 2 }
                                           (Cons { key = "test", value = 1 }
                                            Nil)))
            >>
            assert_list (to_list (test_map <> empty)) (to_list test_map)
            >>
            assert_list (to_list (empty <> test_map)) (to_list test_map)

run tests
