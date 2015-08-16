type Option a = | None | Some a in
type Result e t = | Err e | Ok t in
type List a = | Nil | Cons a (List a) in

let id x = x
and const x = \_ -> x
and flip f = \x y -> f y x
and not x = if x then False else True
and (++) xs ys = case xs of
    | Cons x zs -> Cons x (zs ++ ys)
    | Nil -> ys
and concatMap f xs: (a -> List b) -> List a -> List b = case xs of
    | Cons x ys -> f x ++ concatMap f ys
    | Nil -> Nil
in

type Eq a = {
    (==) : a -> a -> Bool
} in

let eq_Int = {
    (==) = \l r -> l #Int== r
} in
let eq_Float = {
    (==) = \l r -> l #Float== r
} in
let eq_Option: Eq a -> Eq (Option a) = \eq_a -> {
    (==) = \l r ->
        case l of
            | Some l_val ->
                (case r of
                    | Some r_val -> eq_a.(==) l_val r_val
                    | None -> False)
            | None -> 
                (case r of
                    | Some _ -> False
                    | None -> True)
} in
let eq_Result: Eq e -> Eq t -> Eq (Result e t) = \eq_e eq_t -> {
    (==) = \l r ->
        case l of
            | Ok l_val ->
                (case r of
                    | Ok r_val -> eq_t.(==) l_val r_val
                    | Err _ -> False)
            | Err l_val -> 
                (case r of
                    | Ok _ -> False
                    | Err r_val -> eq_e.(==) l_val r_val)
} in
let eq_List: Eq a -> Eq (List a) = \d -> {
    (==) = let f l r = case l of
                | Nil -> case r of
                    | Nil -> True
                    | Cons x y -> False
                | Cons x xs -> case r of
                    | Nil -> False
                    | Cons y ys -> d.(==) x y && f xs ys
            in f
} in
let eq_String: Eq String = {
    (==) = string_eq
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
let ord_String: Ord String = {
    compare = \l r ->
        let o = string_compare l r
        in if o #Int== 0 then EQ else if o #Int== (0 #Int- 1) then LT else GT
} in
let ord_Option: Ord a -> Ord (Option a) = \compare_a -> {
    compare = \l r ->
        case l of
            | Some l_val ->
                (case r of
                    | Some r_val -> compare_a.compare l_val r_val
                    | None -> LT)
            | None -> 
                (case r of
                    | Some r_val -> GT
                    | None -> EQ)
} in
let ord_Result: Ord e -> Ord t -> Ord (Result e t) = \ord_e ord_t -> {
    compare = \l r ->
        case l of
            | Ok l_val ->
                (case r of
                    | Ok r_val -> ord_t.compare l_val r_val
                    | Err _ -> GT)
            | Err l_val -> 
                (case r of
                    | Ok _ -> LT
                    | Err r_val -> ord_e.compare l_val r_val)
} in
let make_Ord ord
    =
    let compare = ord.compare
    in {
        (<=) = \l r -> case compare l r of
            | LT -> True
            | EQ -> True
            | GT -> False,
        (<) = \l r -> case compare l r of
            | LT -> True
            | EQ -> False
            | GT -> False,
        (>) = \l r -> case compare l r of
            | LT -> False
            | EQ -> True
            | GT -> False,
        (=>) = \l r -> case compare l r of
            | LT -> False
            | EQ -> True
            | GT -> True
    }
in
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
type Functor f = {
    map : (a -> b) -> f a -> f b
} in
let functor_Option: Functor Option = {
    map = \f x -> case x of
                    | Some y -> Some (f y)
                    | None -> None
}
and functor_Result: Functor (Result e) = {
    map = \f x -> case x of
                    | Ok y -> Ok (f y)
                    | Err _ -> x
}
and functor_List: Functor List = {
    map =
        let map f xs =
                case xs of
                    | Cons y ys -> Cons (f y) (map f ys)
                    | Nil -> Nil
        in map
} in
type Applicative f = {
    (<*>) : f (a -> b) -> f a -> f b,
    pure : a -> f a
} in
let applicative_Option: Applicative Option = {
    (<*>) = \f x -> case f of
                        | Some g ->
                            (case x of
                                | Some y -> Some (g y)
                                | None -> None)
                        | None -> None,
    pure = \x -> Some x
}
and applicative_Result: Applicative (Result e) = {
    (<*>) = \f x -> case f of
                        | Ok g ->
                            (case x of
                                | Ok y -> Ok (g y)
                                | Err _ -> x)
                        | Err x -> Err x,
    pure = \x -> Ok x
}
and applicative_List: Applicative List = {
    (<*>) =
        let (<*>) f xs =
                case f of
                    | Cons g gs ->
                        functor_List.map g xs ++ (gs <*> xs)
                    | Nil -> Nil
        in (<*>),
    pure = \x -> Cons x Nil
} in
type Monad m = {
    (>>=) : m a -> (a -> m b) -> m b,
    return : a -> m a
} in
let monad_Option: Monad Option = {
    (>>=) = \m f -> case m of
                        | Some x -> f x
                        | None -> None,
    return = \x -> Some x
} in
let monad_List: Monad List = {
    (>>=) = \m f -> concatMap f m,
    return = \x -> Cons x Nil
} in
let monad_IO: Monad IO = {
    (>>=) = io_bind,
    return = io_return
} in
let make_Monad m =
    let { (>>=), return } = m
    //TODO this should not require a second binding
    and bind = m.(>>=)
    in {
        (>>=) = (>>=),
        return = return,
        (>>) = \l r -> l >>= \_ -> r,
        join = \mm -> mm >>= id,
        map = \x f -> x >>= (\y -> return (f x)),
        lift2 = \f lm rm -> bind lm (\l -> rm >>= \r -> f l r)
    }
in
let functor_IO: Functor IO = {
    map = \f m1 -> monad_IO.(>>=) m1 (\x -> monad_IO.return (f x))
} in
let applicative_IO: Applicative IO = {
    (<*>) = \f x ->
            monad_IO.(>>=) f (\g -> monad_IO.(>>=) x (\y -> monad_IO.return (g y))),
    pure = monad_IO.return
} in
type Show a = {
    show : a -> String
} in
let show_Int: Show Int = {
    show = show_Int_prim
} in
let show_Float: Show Float = {
    show = show_Float_prim
} in
let show_String: Show String = {
    show = \x -> x
} in
let show_List: Show a -> Show (List a) = \d ->
    let show xs =
        let show2 ys = case ys of
            | Cons y ys2 -> case ys2 of
                | Cons z zs -> string_append (d.show y) (string_append ", " (show2 ys2))
                | Nil -> string_append (d.show y) "]"
            | Nil -> "]"
        in string_append "[" (show2 xs)
    in { show }
in
{ id, const, flip, not, 
  ord_Option, ord_Result, ord_Float, ord_Int, ord_String, make_Ord,
  eq_List, eq_Option, eq_Result, eq_Float, eq_Int, eq_String,
  num_Int, num_Float,
  functor_Option, functor_Result, functor_List, functor_IO,
  applicative_Option, applicative_Result, applicative_List, applicative_IO,
  monad_Option, monad_List, monad_IO,
  make_Monad,
  show_List
}

