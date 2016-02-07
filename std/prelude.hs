type Option a = | None | Some a in
type Result e t = | Err e | Ok t in
type List a = | Nil | Cons a (List a) in
type Monoid m = {
    (<>): m -> m -> m,
    empty: m
}
in
let monoid_Function m: Monoid b -> (Monoid (a -> b)) = {
    (<>) = \f g -> \x -> m.(<>) (f x) (g x),
    empty = m.empty
}
in
let monoid_List =
    let (<>) xs ys = case xs of
        | Cons x zs -> Cons x (zs <> ys)
        | Nil -> ys
    in {
        (<>),
        empty = Nil
    }
in
let monoid_Option m: Monoid a -> Monoid (Option a) = {
    (<>) = \l r ->
        case l of
            | Some x ->
                (case r of
                    | Some y -> Some (m.(<>) x y)
                    | None -> l)
            | None -> r,
    empty = None
}
in
let monoid_Int_Add = {
    (<>) = \x y -> x #Int+ y,
    empty = 0
}
in
let monoid_Int_Mul = {
    (<>) = \x y -> x #Int* y,
    empty = 1
}
in
let monoid_Float_Add = {
    (<>) = \x y -> x #Float+ y,
    empty = 0.0
}
in
let monoid_Float_Mul = {
    (<>) = \x y -> x #Float* y,
    empty = 1.0
}
in
let id x = x
and const x = \_ -> x
and flip f = \x y -> f y x
and not x = if x then False else True
and concatMap f xs: (a -> List b) -> List a -> List b = case xs of
    | Cons x ys -> monoid_List.(<>) (f x) (concatMap f ys)
    | Nil -> Nil
and foldl f x xs = case xs of
    | Cons y ys -> foldl f (f x y) ys
    | Nil -> x
and foldr f x xs = case xs of
    | Cons y ys -> f y (foldr f x ys)
    | Nil -> x
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
                | Nil -> (case r of
                    | Nil -> True
                    | Cons x y -> False)
                | Cons x xs -> case r of
                    | Nil -> False
                    | Cons y ys -> d.(==) x y && f xs ys
            in f
} in

type Ordering = | LT | EQ | GT
in
let monoid_Ordering = {
    (<>) = \x y ->
        case x of
            | EQ -> y
            | _ -> x,
    empty = EQ
}
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
            | EQ -> False
            | GT -> True,
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
    (/) : a -> a -> a,
    negate: a -> a
} in
let num_Int: Num Int = {
    (+) = monoid_Int_Add.(<>),
    (-) = \l r -> l #Int- r,
    (*) = monoid_Int_Mul.(<>),
    (/) = \l r -> l #Int/ r,
    negate = \x -> 0 #Int- x
} in
let num_Float: Num Float = {
    (+) = monoid_Float_Add.(<>),
    (-) = \l r -> l #Float- r,
    (*) = monoid_Float_Mul.(<>),
    (/) = \l r -> l #Float/ r,
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
                        monoid_List.(<>) (functor_List.map g xs) (gs <*> xs)
                    | Nil -> Nil
        in (<*>),
    pure = \x -> Cons x Nil
}
in
type Alternative f = {
    (<|>) : f a -> f a -> f a,
    empty : f a
}
in
let alternative_Option: Alternative Option = {
    (<|>) = \x y ->
        case x of
            | Some _ -> x
            | None -> y,
    empty = None
}
and alternative_List: Alternative List = {
    (<|>) = monoid_List.(<>),
    empty = Nil
}
in
let make_Alternative fun app alt =
    let { (<|>), empty } = alt
    and { (<*>), pure } = app
    in
    let many x =
        let many_v _ = some_v () <|> pure Nil
        and some_v _ = fun.map (\h l -> Cons h l) x <*> many_v ()
        in many_v ()
    and some x =
        let many_v _ = some_v () <|> pure Nil
        and some_v _ = fun.map (\h l -> Cons h l) x <*> many_v ()
        in some_v ()
    in {
        (<|>),
        empty,
        many,
        some
    }
in
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
    in
    let (>>) l r = l >>= \_ -> r
    in
    let forM_ xs f = case xs of
            | Cons y ys ->
                f y >> forM_ ys f
            | Nil -> return ()
    in {
        (>>=) = (>>=),
        return = return,
        (>>),
        join = \mm -> mm >>= id,
        map = \x f -> x >>= (\y -> return (f x)),
        lift2 = \f lm rm -> lm >>= \l -> rm >>= \r -> f l r,
        forM_
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
    show = prim.show_Int
} in
let show_Float: Show Float = {
    show = prim.show_Float
} in
let (++) = string_prim.append
in
let show_List: Show a -> Show (List a) = \d ->
    let show xs =
        let show2 ys = case ys of
            | Cons y ys2 -> case ys2 of
                | Cons z zs -> d.show y ++ ", " ++ show2 ys2
                | Nil -> d.show y ++ "]"
            | Nil -> "]"
        in "[" ++ show2 xs
    in { show }
in
let show_Option: Show a -> Show (Option a) = \d ->
    let show o =
            case o of
                | Some x -> "Some (" ++ d.show x ++ ")"
                | None -> "None"
    in { show }
in
{
    Eq,
    Ord,
    Monoid,
    Ordering,
    Option,
    Result,
    List,
    Functor,
    Applicative,
    Alternative,
    Monad,
    Num,
    Show,
    id, const, flip, not,
    foldl, foldr,
    ord_Option, ord_Result, ord_Float, ord_Int, make_Ord,
    eq_List, eq_Option, eq_Result, eq_Float, eq_Int,
    monoid_Function, monoid_List, monoid_Option,
    monoid_Int_Add, monoid_Int_Mul, monoid_Float_Add, monoid_Float_Mul,
    num_Int, num_Float,
    functor_Option, functor_Result, functor_List, functor_IO,
    applicative_Option, applicative_Result, applicative_List, applicative_IO,
    alternative_Option, alternative_List,
    make_Alternative,
    monad_Option, monad_List, monad_IO,
    make_Monad,
    show_Int, show_Float, show_List, show_Option
}

