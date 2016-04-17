let prelude = import "std/prelude.hs"
and { Num, Option, Eq, Ord, Ordering, Monoid, Show } = prelude
and (==) = prelude.eq_Int.(==)
and monoid = {
    (<>) = string_prim.append,
    empty = ""
}
in
let starts_with haystack needle =
    case string_prim.find haystack needle of
        | Some i -> i == 0
        | None -> False
and ends_with haystack needle =
    case string_prim.rfind haystack needle of
        | Some i -> i == string_prim.length haystack - string_prim.length needle
        | None -> False
in
let ord: Ord String = {
    compare = string_prim.compare
}
in
let show: Show String = {
    show = prelude.id
}
in {
    length = string_prim.length,
    find = string_prim.find,
    rfind = string_prim.rfind,
    trim = string_prim.trim,
    trim_left = string_prim.trim_left,
    trim_right = string_prim.trim_right,
    compare = string_prim.compare,
    eq = { (==) = string_prim.eq },
    ord,
    show,
    slice = string_prim.slice,
    starts_with,
    ends_with,
    monoid
}
