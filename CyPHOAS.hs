{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}

-- a currently failing attempt to model using PHOAS

data Cy_ f v =
    Cy (v -> Cy_ f v)
    | D (f (Cy_ f v))
    | Var v

newtype Cy f = MakeCy (forall v. Cy_ f v)

data IListF x = Cons Int x deriving (Show, Functor)

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

inf12 = MakeCy $ Cy (\v -> D $ Cons 1 (D $ Cons 2 $ Var v))

inf34 = fold (ListC (\x r -> D $ Cons (x+1) r)) inf12


newtype StringF x = MkStringF String

-- x = ListC2 (\k (x,y) -> (D $ MkStringF "a", D $ Cons 1 $ y))


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


class FoldTry (f :: * -> *) where
    data CataTry f a
    data CataTry2 f a b
    elimFTry :: CataTry f a -> (Cy_ f v -> a) -> f (Cy_ f v) -> a

instance FoldTry IListF where
    newtype CataTry IListF a = ListCTry (Int -> a -> a)
    newtype CataTry2 IListF a b = ListCTry2 (Int -> (a,b) -> (a,b))
    elimFTry (ListCTry cata) self (Cons x xs) = cata x (self xs)

foldTry' :: FoldTry f => CataTry f (Cy_ g v) -> Cy_ f v -> Cy_ g v
foldTry' cata (Cy f)   = Cy (\v -> foldTry' cata (f v))
foldTry' cata (D y)    = elimFTry cata (foldTry' cata) y
foldTry' _    (Var v)  = Var v

foldTry :: FoldTry f1 => CataTry f1 (Cy_ g v) -> Cy f1 -> Cy_ g v
foldTry cata (MakeCy cy) = foldTry' cata cy

foldTry2_ :: FoldTry f1 => CataTry f1 (Cy_ g v) -> Cy f1 -> Cy_ g v
foldTry2_ cata (MakeCy cy) = foldTry' cata cy

inf34' = MakeCy $ foldTry (ListCTry (\x r -> D $ Cons (x+1) r)) inf12

f = ListCTry2 (\x (r1,r2) -> (case r2 of Cons x xs -> xs, Cons (x+1) $ D r2))

-- foldTry2' :: 
--     FoldTry f => 
--     CataTry2 f (Cy_ g1 v1) (Cy_ g2 v2) 
--     -> Cy_ f v 
--     -> (v1,v2) -> (Cy_ g1 v1, Cy_ g2 v2)

-- foldTry2' cata (Cy f)   = \(v1,v2) -> foldTry2' cata (f v1)
-- foldTry2' cata (D y)    = 
-- foldTry2' _    (Var v)  = 


-- Broken cy-pair

newtype Cy2 f g =
    MakeCy2 {extCy2::forall v w. (v,w) -> (Cy_ f v, Cy_ g v)}

-- inf1234 = MakeCy2 $
--     \(v,w) -> 
--     (
--         D $ Cons 1 $ D $ Cons 2 $ Var w,
--         D $ Cons 3 $ D $ Cons 4 $ Var v
--     )


-- -- Broken bekic
-- bekic :: Cy2 f g -> (Cy2_ f v (Cy2_ g w v), Cy2_ g w1 (Cy2_ f v2 (Cy2_ g w2 v2)))
-- bekic cy2 =
--     (
--         Cy2 (\v -> 
--                 let s = Cy2 (\w -> snd (extCy2 cy2) (v,w)) in
--                 fst (extCy2 cy2) (v,s)
--             )
--         ,
--         Cy2 (\w ->
--                 let s v = Cy2 (\w -> snd (extCy2 cy2) (v,w)) in
--                 let t = Cy2 (\v -> fst (extCy2 cy2) (v,s v)) in
--                 snd (extCy2 cy2) (t,w)
--             )
--     )

data (:+:) f g x = LeftF (f x) | RightF (g x) deriving Functor


data DB = Idx | Level

-- first order binding (either w/ DeBruijn index or level)
data CyFO (db :: DB) f =
      CyFO (CyFO db f)
    | DFO (f (CyFO db f))
    | VarFO Int

type CyIdx f = CyFO Idx f

newtype CyIdx2 f g = CyFO2 (CyIdx f, CyIdx g)

-- toFO2_ :: Functor f => Int -> Cy2_ f Int Int -> CyFO Level f
-- toFO2_ cnt (Cy2 f) = CyFO (toFO2_ (cnt+1) (f cnt))
-- toFO2_ cnt (DD d)  = DFO $ fmap (toFO2_ cnt) d
-- toFO2_ cnt (VarUs v) = VarFO v
-- toFO2_ cnt (VarOt v) = VarFO v


----------------------------------------
-- translating back and forth from/to the first-order term
-- (which might not help at all)
----------------------------------------

toFO :: Functor f => Cy f -> CyFO 'Level f
toFO (MakeCy cy) = toFO_ 0 cy

toFO_ :: Functor f => Int -> Cy_ f Int -> CyFO Level f
toFO_ cnt (Cy f) = CyFO (toFO_ (cnt+1) (f cnt))
toFO_ cnt (D d)  = DFO $ fmap (toFO_ cnt) d
toFO_ cnt (Var v) = VarFO v 

fromFO_ :: Functor f => [v] -> CyFO Idx f -> Cy_ f v
fromFO_ vars (CyFO c)  = Cy (\v -> fromFO_ (v:vars) c)
fromFO_ vars (DFO c)   = D $ fmap (fromFO_ vars) c
fromFO_ vars (VarFO n) = Var (vars !! n)

fromFO :: Functor f => CyFO Idx f -> Cy f
fromFO c = MakeCy (fromFO_ [] c)

levelToIdx :: Functor f => Int -> CyFO Level f -> CyFO Idx f
levelToIdx cnt (CyFO c)  = CyFO (levelToIdx (cnt+1) c)
levelToIdx cnt (DFO c)   = DFO $ fmap (levelToIdx cnt) c
levelToIdx cnt (VarFO n) = VarFO (cnt - n - 1)

showCyFORaw :: ((CyFO db f -> String) -> f (CyFO db f) -> String) -> CyFO db f -> String
showCyFORaw showD (CyFO c) = 
    "cy(. " ++ showCyFORaw showD c ++ ")"
showCyFORaw showD (DFO c) =
    showD (showCyFORaw showD) c
showCyFORaw _     (VarFO n) =
    "_" ++ show n

showCyFO :: Int -> ((CyFO Idx f -> String) -> f (CyFO Idx f) -> String) -> CyFO Idx f -> String
showCyFO cnt showD (CyFO c) = 
    let var = "x" ++ show cnt in
    "cy(" ++ var ++ ". " ++ showCyFO (cnt+1) showD c ++ ")"
showCyFO cnt showD (DFO c) =
    showD (showCyFO cnt showD) c
showCyFO cnt _     (VarFO n) =
    "x" ++ show (cnt - n)

showIListFO :: CyFO Idx IListF -> String
showIListFO = showCyFO 0 (\showD (Cons x xs) -> "Cons(" ++ show x ++ ", " ++ showD xs ++ ")")

showIListFORaw :: CyFO db IListF -> String
showIListFORaw = showCyFORaw (\showD (Cons x xs) -> "Cons(" ++ show x ++ ", " ++ showD xs ++ ")")


main = do
    print $ showIList inf12
    print $ showIList inf34

-- *Main> main
-- "cy(x0.Cons(1,Cons(2,x0)))"
-- "cy(x0.Cons(2,Cons(3,x0)))"
-- *Main> 
