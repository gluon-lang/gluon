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
let eq_Option: (a -> a -> Bool) -> Eq (Option a) = \eq_a -> {
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

type Ordering = | LT | EQ | GT
in

type Ord a = {
    compare : a -> a -> Ordering
} in

let ord_Int = {
    compare = \l r ->
        if l #Int< r
        then LT
        else if l #Int== r
        then EQ
        else GT
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
        case l of
            | Some l_val ->
                case r of
                    | Some r_val -> compare_a l_val r_val
                    | None -> LT
            | None -> 
                case r of
                    | Some r_val -> GT
                    | None -> EQ
} in
type Num a = {
    (+) : a -> a -> a,
    (-) : a -> a -> a,
    (*) : a -> a -> a,
    negate: a -> a
} in
let num_Int: Num Int = {
    (+) = \l r -> l #Int+ r,
    (-) = \l r -> l #Int- r,
    (*) = \l r -> l #Int* r,
    negate = \x -> 0 #Int- x
} in
let num_Float: Num Float = {
    (+) = \l r -> l #Float+ r,
    (-) = \l r -> l #Float- r,
    (*) = \l r -> l #Float* r,
    negate = \x -> 0.0 #Float- x
} in
{ ord_Option = ord_Option, ord_Float = ord_Float, ord_Int = ord_Int, eq_Option = eq_Option, eq_Float = eq_Float, eq_Int = eq_Int, num_Int = num_Int, num_Float = num_Float }

