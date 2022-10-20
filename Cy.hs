{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

data IListF x = Cons Int x deriving Functor

class Functor f => Fold (f :: * -> *) where
    data Cata f a
    collectF :: Monoid a => Cata f a
    elimF :: Cata f a -> (Cy f -> a) -> f (Cy f) -> a

instance Fold IListF where
    newtype Cata IListF a = ListC (Int -> a -> a)
    collectF = ListC (const id)
    elimF (ListC cata) self (Cons x xs) = cata x (self xs)

showListF :: Cata IListF [Char]
showListF = ListC (\k s -> "Cons(" ++ show k ++ "," ++ s ++ ")")

-- first order binding (either w/ DeBruijn index or level)
data Cy f =
      Cy (Cy f)
    | D (f (Cy f))
    | Var Int

newtype StringF t = MkStringF String

fold :: Fold f => Cata f (Cy g) -> Cy f -> Cy g
fold cata (Cy f)   = Cy (fold cata f)
fold cata (D y)    = elimF cata (fold cata) y
fold _    (Var v)  = Var v


incr' :: Functor f => Int -> Cy f -> Cy f
incr' cnt (Cy f)  = Cy (incr' (cnt+1) f)
incr' cnt (D y)   = D (fmap (incr' cnt) y) 
incr' cnt (Var n) = if n >= cnt then Var (n+1) else Var n

incr :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incr (cy1,cy2) = (incr' 0 cy1, incr' 0 cy2)

fold2' :: (Fold f, Functor g1, Functor g2) => 
    Cata f (Cy g1, Cy g2)
    -> [(Cy g1, Cy g2)] 
    -> Cy f 
    -> (Cy g1, Cy g2)
fold2' cata vars (Cy f)  = 
    -- bekic
    let (_,s0) = fold2' cata ((Var 0, Var 0) : map incr vars) f
        (t,_)  = fold2' cata ((Var 0, Cy s0) : map incr vars) f
        (_,s)  = fold2' cata ((Cy t, Var 0) : map incr vars) f
    in (Cy t, Cy s)
fold2' cata vars (D y)   = 
    elimF cata (fold2' cata vars) y
fold2' _    vars (Var n)
    | n < length vars - 1 
                       = (Var n, Var n)
    | length vars - 1 <= n && n < length vars * 2 - 1
                       = vars !! (n - length vars + 1)
    | otherwise        = error "fold2: impossible - unbound recursion var"

fold2 :: (Fold f, Fold g1, Fold g2) => Cata f (Cy g1, Cy g2) -> Cy f -> (Cy g1, Cy g2)
fold2 cata cy = let (x,y) = fold2' cata [] cy in (clean0 x, clean0 y)

fvars :: Fold f => Cy f -> [Int]
fvars (Cy f)  = filter (/=0) (fvars f)
fvars (D y)   = elimF collectF fvars y
fvars (Var v) = [v]

-- clean up unused bindings
clean0 :: Fold f => Cy f -> Cy f
clean0 (Cy f) = if 0 `elem` fvars f then Cy f else f
clean0 (D y)  = D $ fmap clean0 y
clean0 (Var v) = Var v

-- print w/ De Bruijn indices
showCyRaw :: Fold f => Cata f String -> Cy f -> String
showCyRaw cata (Cy f)   = "cy(. " ++ showCyRaw cata f ++ ")"
showCyRaw cata (D c)    = elimF cata (showCyRaw cata) c
showCyRaw _    (Var n) = "Var " ++ show n

-- standard printing
showCy' :: Fold f => Int -> Cata f String -> Cy f -> String
showCy' cnt cata (Cy f)   = "cy(x" ++ show cnt ++ ". " ++ showCy' (cnt+1) cata f ++ ")"
showCy' cnt cata (D c)    = elimF cata (showCy' cnt cata) c
showCy' cnt _    (Var n) = "x" ++ show (cnt - n - 1)

showCy = showCy' 0

showIList :: Cy IListF -> String
showIList = showCy showListF

inf12 = Cy (D $ Cons 1 (D $ Cons 2 $ Var 0))

inf23 = fold (ListC (\x r -> D $ Cons (x+1) r)) inf12

tailcy = ListC (\k (x,y) -> (y, D $ Cons k y))

inf21_ = fold2 tailcy inf12

main = do
    print $ showCyRaw showListF inf12
    print $ showIList inf23
    print $ showIList $ fst inf21_
    print $ showIList $ snd inf21_
-- *Main> main
-- "cy(x0.Cons(1,Cons(2,x0)))"
-- "cy(x0.Cons(2,Cons(3,x0)))"
-- *Main> 



-- Statically checked de Bruijn indices

data N = Z_ | S_ N

data Idx n where
    Z :: Idx n
    S :: Idx n -> Idx (S_ n)

data CyN (n :: N) f where
    CyN :: CyN (S_ n) f -> CyN n f
    DN :: f (CyN n f) -> CyN n f
    VarN :: Idx n -> CyN (S_ n) f

data TreeF t = Node Int t t

inft1 = CyN $ DN $ Node 1 (VarN Z) $ VarN (S Z)
