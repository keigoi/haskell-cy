{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- A (partial) implementation of M. Hamana's cy rewriting system:
-- Cyclic Datatypes modulo Bisimulation based on Second-Order Algebraic Theories
-- Logical Methods in Computer Science, November 15, 2017, Volume 13, Issue 4
-- https://doi.org/10.23638/LMCS-13(4:8)2017

-- cy (cyclic data structure), binding w/ DeBruijn index
data Cy f =
      Cy (Cy f)
    | D (f (Cy f))
    | Var Int

class Functor f => FoldCy (f :: * -> *) where
    data Cata f a
    collectF :: Monoid a => Cata f a
    elimF :: Cata f a -> (t -> a) -> f t -> a

class FoldCy f => ShowFoldCy f where
    showF :: Cata f String

fold :: FoldCy f => Cata f (Cy g) -> Cy f -> Cy g
fold cata (Cy f)   = Cy (fold cata f)
fold cata (D y)    = elimF cata (fold cata) y
fold _    (Var v)  = Var v

incr' :: Functor f => Int -> Cy f -> Cy f
incr' cnt (Cy f)  = Cy (incr' (cnt+1) f)
incr' cnt (D y)   = D (fmap (incr' cnt) y) 
incr' cnt (Var n) = if n >= cnt then Var (n+1) else Var n

incrVars :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incrVars (cy1,cy2) = (incr' 0 cy1, incr' 0 cy2)

fold2' :: (FoldCy f, Functor g1, Functor g2) => 
    Cata f (Cy g1, Cy g2)
    -> [(Cy g1, Cy g2)] 
    -> Cy f 
    -> (Cy g1, Cy g2)
fold2' cata vars (Cy f)  = 
    -- bekic
    let (_,s0) = fold2' cata ((Var 0, Var 0) : map incrVars vars) f
        (t,_)  = fold2' cata ((Var 0, Cy s0) : map incrVars vars) f
        (_,s)  = fold2' cata ((Cy t, Var 0) : map incrVars vars) f
    in (Cy t, Cy s)
fold2' cata vars (D y)   = 
    elimF cata (fold2' cata vars) y
fold2' _    vars (Var n)
    | n < length vars - 1 
                       = (Var n, Var n)
    | length vars - 1 <= n && n < length vars * 2 - 1
                       = vars !! (n - length vars + 1)
    | otherwise        = error "fold2: impossible - unbound recursion var"

fold2 :: (FoldCy f, FoldCy g1, FoldCy g2) => Cata f (Cy g1, Cy g2) -> Cy f -> (Cy g1, Cy g2)
fold2 cata cy = let (x,y) = fold2' cata [] cy in (clean0 x, clean0 y)

fvars :: FoldCy f => Cy f -> [Int]
fvars (Cy f)  = filter (/=0) (fvars f)
fvars (D y)   = elimF collectF fvars y
fvars (Var v) = [v]

-- clean up unused bindings
clean0 :: FoldCy f => Cy f -> Cy f
clean0 (Cy f) = if 0 `elem` fvars f then Cy f else f
clean0 (D y)  = D $ fmap clean0 y
clean0 (Var v) = Var v

-- print w/ De Bruijn indices
showCyRaw :: FoldCy f => Cata f String -> Cy f -> String
showCyRaw cata (Cy f)   = "cy(. " ++ showCyRaw cata f ++ ")"
showCyRaw cata (D c)    = elimF cata (showCyRaw cata) c
showCyRaw _    (Var n) = "Var " ++ show n

-- standard printing
showCy' :: ShowFoldCy f => Int -> Cy f -> String
showCy' cnt (Cy f)   = "cy(x" ++ show cnt ++ ". " ++ showCy' (cnt+1) f ++ ")"
showCy' cnt (D c)    = elimF showF (showCy' cnt) c
showCy' cnt (Var n) = "x" ++ show (cnt - n - 1)

showCy :: Cy IListF -> String
showCy = showCy' 0

-- infinite list
data IListF x = Cons Int x deriving Functor

instance FoldCy IListF where
    newtype Cata IListF a = ListC (Int -> a -> a)
    collectF = ListC (const id)
    elimF (ListC cata) self (Cons x xs) = cata x (self xs)

instance ShowFoldCy IListF where
    showF = ListC (\k s -> "Cons(" ++ show k ++ "," ++ s ++ ")")

inf12 = Cy (D $ Cons 1 (D $ Cons 2 $ Var 0))

inf23 = fold (ListC (\x r -> D $ Cons (x+1) r)) inf12

tailIL = fst . fold2 (ListC (\k (x,y) -> (y, D $ Cons k y)))

main = do
    putStrLn $ showCy inf12
    putStrLn $ showCy inf23
    putStrLn $ showCy $ tailIL inf12
    putStrLn $ showCy $ tailIL inf23

-- *Main> main
-- cy(x0. Cons(1,Cons(2,x0)))
-- cy(x0. Cons(2,Cons(3,x0)))
-- Cons(2,cy(x0. Cons(1,Cons(2,x0))))
-- Cons(3,cy(x0. Cons(2,Cons(3,x0))))
-- *Main> 
