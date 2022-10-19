{-# LANGUAGE Rank2Types, TypeFamilies #-}

data Cy_ f v =
    Cy (v -> Cy_ f v)
    | D (f (Cy_ f v))
    | Var v

newtype Cy f = MakeCy (forall v. Cy_ f v)

data Cy2_ f v w =
    Cy2 (v -> Cy2_ f v w)
    | DD (f (Cy2_ f v w))
    | VarUs v
    | VarOt w

newtype Cy2 f g =
    MakeCy2 {extCy2::forall v w. ((v,w) -> Cy2_ f v w, (v,w) -> Cy2_ g w v)}

data IListF x = Cons Int x deriving Show

inf12 = MakeCy $ Cy (\v -> D $ Cons 1 (D $ Cons 2 $ Var v))

-- inf1234 = MakeCy2 $ 
--     (
--         \(v,w) -> DD $ Cons 1 $ DD $ Cons 2 $ VarOt w, 
--         \(v,w) -> DD $ Cons 3 $ DD $ Cons 4 $ VarOt v
--     )

class Fold (f :: * -> *) where
    data Cata f (g :: * -> *)
    elimF :: Cata f g -> (Cy_ f v -> Cy_ g v) -> f (Cy_ f v) -> Cy_ g v

instance Fold IListF where
    newtype Cata IListF g = ListC (forall v. Int -> Cy_ g v -> Cy_ g v)
    elimF (ListC cata) self (Cons x xs) = cata x (self xs)

fold' :: Fold f => Cata f g -> Cy_ f v -> Cy_ g v
fold' cata (Cy f)   = Cy (fold' cata . f)
fold' cata (D y)    = elimF cata (fold' cata) y
fold' _    (Var v)  = Var v

fold :: Fold f1 => Cata f1 f2 -> Cy f1 -> Cy f2
fold cata (MakeCy cy) = MakeCy (fold' cata cy)

bekic :: Cy2 f g -> (Cy2_ f v (Cy2_ g w v), Cy2_ g w1 (Cy2_ f v2 (Cy2_ g w2 v2)))
bekic cy2 =
    (
        Cy2 (\v -> 
                let s = Cy2 (\w -> snd (extCy2 cy2) (v,w)) in
                fst (extCy2 cy2) (v,s)
            )
        ,
        Cy2 (\w ->
                let s v = Cy2 (\w -> snd (extCy2 cy2) (v,w)) in
                let t = Cy2 (\v -> fst (extCy2 cy2) (v,s v)) in
                snd (extCy2 cy2) (t,w)
            )
    )

inf34 = fold (ListC (\x r -> D $ Cons (x+1) r)) inf12

-- これは fold で定義できそう (というか，できるべき)

showCy_ :: ((Cy_ f String -> String) -> f (Cy_ f String) -> String) -> Int -> Cy_ f String -> String
showCy_ showD cnt (Cy f) = 
    let var = "x" ++ show cnt in
    "cy(" ++ var ++ "." ++ showCy_ showD (cnt+1) (f var) ++ ")"
showCy_ showD cnt (D d) = showD (showCy_ showD cnt) d
showCy_ _ _       (Var s) = s

showIList_ :: (t -> [Char]) -> IListF t -> [Char]
showIList_ showCont (Cons x xs) = "Cons(" ++ show x ++ "," ++ showCont  xs ++ ")"

showIList :: Cy IListF -> String
showIList (MakeCy cy) = showCy_ showIList_ 0 cy


main = do
    print $ showIList inf12
    print $ showIList inf34

-- *Main> main
-- "cy(x0.Cons(1,Cons(2,x0)))"
-- "cy(x0.Cons(2,Cons(3,x0)))"
-- *Main> 
