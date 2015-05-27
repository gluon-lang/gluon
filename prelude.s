
type Option a = | None | Some a in

type Eq a = {
    (==) : a -> a -> Bool
} in

let eq_Int = {
    (==) = \l r -> l #Int== r
} in
let eq_Float = {
    (==) = \l r -> l #Float== r
} in
let eq_Option = \eq_a -> {
    (==) = \l r ->
        case l of
            | Some l_val ->
                case r of
                    | Some r_val -> eq_a l_val r_val
                    | None -> False
            | None -> 
                case r of
                    | Some _ -> False
                    | None -> True
} in

let any p xs =
    let (+) l r = l #Int+ r in
    let any_ i = if i >= array_length xs
                 then False
                 else if p xs[i]
                 then True
                 else any_ (i + 1)
                 
    in any_ 0
in

let array_Eq = \a_eq -> {
    (==) = \l r -> any (\(l, r) -> a_eq l r) $ zip l r
} in

type Ordering = LT | EQ | GT
in

type Ord a = {
    compare : a -> a -> Ordering
} in

let ord_Int = {
    compare = \l r -> {
        if l #Int< r {
            LT
        }
        else if l #Int== r {
            EQ
        }
        else {
            GT
        }
    }
} in

let ord_Float = {
    compare = \l r ->
        if l #Float< r
        then LT
        else if l #Float== r
        then EQ
        else GT
} in
let ord_Option = \compare_a -> {
    compare = \l r ->
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { compare(l_val, r_val) }
                    None() => { LT() }
                }
            }
            None() => {
                match r {
                    Some(r_val) => { GT() }
                    None() => { EQ() }
                }
            }
        }
    }
} in
type Num a = {
    (+) : a -> a -> a,
    (-) : a -> a -> a,
    (*) : a -> a -> a,
    negate: a -> a
} in
let num_Int: Num Int = {
    (+) = \l r -> l #Int+ r,
    (*) = \l r -> l #Int* r,
    (-) = \l r -> l #Int- r,
    negate = \x -> 0 #Int- x
} in
let num_Float: Num Float = {
    (+) = \l r -> l #Float+ r,
    (*) = \l r -> l #Float* r,
    (-) = \l r -> l #Float- r,
    negate = \x -> 0.0 #Float- x
} in
{ ord_Option, ord_Float, ord_Int, eq_Option, eq_Float, eq_Int, num_Int, num_Float }

