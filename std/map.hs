type Map k a = | Bin k a (Map k a) (Map k a)
               | Tip
in let empty = Tip
in let singleton k v = Bin k v empty empty
in \(<) (==) ->
    let find k m = case m of
            | Bin k2 v l r ->
                if k < k2 then find k l
                else if k == k2 then Some v
                else find k r
            | Tip -> None
    in let insert k v m = case m of
        | Bin k2 v2 l r ->
                if k < k2 then Bin k2 v2 (insert k v l) r
                else if k == k2 then Bin k v l r
                else Bin k2 v2 l (insert k v r)
        | Tip -> Bin k v empty empty
    in let (++) l r = case l of
        | Bin lk lv ll lr -> (case r of
            | Bin rk rv rl rr ->
                if lk < rk
                then Bin lk lv ll (lr ++ r)
                else if lk == rk
                then Bin lk lv (ll ++ rl) (lr ++ rr)
                else Bin lk lv (ll ++ r) lr
            | Tip -> l)
        | Tip -> case r of
            | Bin a b c d -> r
            | Tip -> empty
    in { empty, singleton, find, insert, (++) }
