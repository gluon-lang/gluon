let { Num, Option, Eq } = prelude
and (==) = prelude.eq_Int.(==)
and { (+), (-), (*) } = prelude.num_Int
in
let starts_with haystack needle =
    case string_prim.find haystack needle of
        | Some i -> i == 0
        | None -> False
and ends_with haystack needle =
    case string_prim.rfind haystack needle of
        | Some i -> i == string_prim.length haystack - string_prim.length needle
        | None -> False
in {
    length = string_prim.length,
    find = string_prim.find,
    rfind = string_prim.rfind,
    trim = string_prim.trim,
    compare = string_prim.compare,
    append = string_prim.append,
    eq = { (==) = string_prim.eq },
    slice = string_prim.slice,
    starts_with
}
