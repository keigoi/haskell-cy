{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}

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
    showCy :: Cy f -> String
    showCy = showCy' 0


-- standard printing
showCy' :: ShowFoldCy f => Int -> Cy f -> String
showCy' cnt (Cy f)   = "cy(x" ++ show cnt ++ ". " ++ showCy' (cnt+1) f ++ ")"
showCy' cnt (D c)    = elimF showF (showCy' cnt) c
showCy' cnt (Var n) = "x" ++ show (cnt - n - 1)


fold :: FoldCy f => Cata f (Cy g) -> Cy f -> Cy g
fold cata (Cy f)   = Cy (fold cata f)
fold cata (D y)    = elimF cata (fold cata) y
fold _    (Var v)  = Var v

incrFVar :: Functor f => Int -> Cy f -> Cy f
incrFVar cnt (Cy f)  = Cy (incrFVar (cnt+1) f)
incrFVar cnt (D y)   = D (fmap (incrFVar cnt) y) 
incrFVar cnt (Var n) = if n >= cnt then Var (n+1) else Var n

incrFVarPair :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incrFVarPair (cy1,cy2) = (incrFVar 0 cy1, incrFVar 0 cy2)

fold2' :: (FoldCy f, Functor g1, Functor g2) => 
    Cata f (Cy g1, Cy g2)
    -> [(Cy g1, Cy g2)] 
    -> Cy f 
    -> (Cy g1, Cy g2)
fold2' cata vars (Cy f)  = 
    -- bekic
    let (_,s0) = fold2' cata ((Var 0, Var 0) : map incrFVarPair vars) f
        (t,_)  = fold2' cata ((Var 0, Cy s0) : map incrFVarPair vars) f
        (_,s)  = fold2' cata ((Cy t, Var 0) : map incrFVarPair vars) f
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

-- data (f :: * -> *) :+ g
-- data (f :: * -> *) :+: (g :: * -> *)

-- infixr 3 :+

-- data CyTup gs where
--     (:+) :: Cy g -> CyTup gs -> CyTup (g :+ gs)
--     (:+:) :: Cy f -> Cy g -> CyTup (f :+: g)

-- class FoldCyTup gs where
--     genVars :: Int -> CyTup gs
--     bindRecs :: CyTup gs -> CyTup gs 
--     mapTup :: (forall g. FoldCy g => Cy g -> Cy g) -> CyTup gs -> CyTup gs

-- instance (FoldCy f, FoldCy g) => FoldCyTup (f :+: g) where
--     genVars i = Var i :+: Var i
--     bindRecs (f :+: g) = Cy f :+: Cy g
--     mapTup f (c :+: d) = f c :+: f d

-- instance (FoldCy g, FoldCyTup gs) => FoldCyTup (g :+ gs) where
--     genVars i = (:+) (Var i) (genVars i)
--     bindRecs ((:+) c cs) = (:+) (Cy c) (bindRecs cs)
--     mapTup f ((:+) c cs) = (:+) (f c) (mapTup f cs)

-- incrFVarTup :: (FoldCy g, FoldCyTup gs) => CyTup (g :+ gs) -> CyTup (g :+ gs)
-- incrFVarTup ((:+) cy1 cys) = (:+) (incrFVar 0 cy1) (mapTup (incrFVar 0) cys)

-- foldMany' :: (FoldCy f, FoldCy g, FoldCyTup gs) => Cata f (CyTup (g :+ gs)) -> [CyTup (g :+ gs)] -> Cy f -> CyTup (g :+ gs)
-- foldMany' cata vars (Cy f)  = 
--     -- bekic
--     let ((:+) _ ss0) = foldMany' cata ((:+) (Var 0) (genVars 0) : map incrFVarTup vars) f
--         ((:+) t _)   = foldMany' cata ((:+) (Var 0) (bindRecs ss0) : map incrFVarTup vars) f
--         ((:+) _ ss)  = foldMany' cata ((:+) (Cy t)  (genVars 0) : map incrFVarTup vars) f
--     in (:+) (Cy t) ss
-- foldMany' cata vars (D y)   = 
--     elimF cata (foldMany' cata vars) y
-- foldMany' _    vars (Var n)
--     | n < length vars - 1 
--                        = (:+) (Var n) (genVars n)
--     | length vars - 1 <= n && n < length vars * 2 - 1
--                        = vars !! (n - length vars + 1)
--     | otherwise        = error "fold2: impossible - unbound recursion var"

-- foldMany :: (FoldCy f, FoldCy g, FoldCyTup gs) => Cata f (CyTup (g :+ gs)) -> Cy f -> CyTup (g :+ gs)
-- foldMany cata = mapTup clean0 . foldMany' cata []

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

-- infinite list
data IListF x = Cons Int x deriving Functor

instance FoldCy IListF where
    newtype Cata IListF a = IListC (Int -> a -> a)
    collectF = IListC (const id)
    elimF (IListC cata) self (Cons x xs) = cata x (self xs)

instance ShowFoldCy IListF where
    showF = IListC (\k s -> "Cons(" ++ show k ++ "," ++ s ++ ")")

inf12 = Cy (D $ Cons 1 (D $ Cons 2 $ Var 0))

inf23 = fold (IListC (\x r -> D $ Cons (x+1) r)) inf12

tailIL = fst . fold2 (IListC (\k (x,y) -> (y, D $ Cons k y)))


-- tailIL' :: Cy IListF ->　CyTup (IListF :+ IListF :+: IListF) 
-- tailIL' = foldMany (IListC (\k (_ :+ (_ :+: z)) -> z :+ z :+: D (Cons k z)))

-- tailIL2 :: Cy IListF -> Cy IListF
-- tailIL2 = fstTup . tailIL'

data CStringF t =
    A t
    | B t
    | Eps
    | Or t t deriving Functor

instance FoldCy CStringF where
  data Cata CStringF a = CStringC {caseA :: a -> a, caseB :: a -> a, caseEps :: a, caseOr :: a -> a -> a}
  collectF = CStringC id id mempty (<>)
  elimF CStringC {caseA, caseB, caseEps, caseOr} self cstr = case cstr of
    A s -> caseA (self s)
    B s -> caseB (self s)
    Eps -> caseEps
    Or s1 s2 -> caseOr (self s1) (self s2)

instance ShowFoldCy CStringF where
    showF = CStringC {caseA=("A."++), caseB=("B."++), caseEps="ε", caseOr= \s1 s2 -> "("++s1++"|"++s2++")"}

data ABoolF t = True_ | False_ deriving Functor

instance FoldCy ABoolF where
    data Cata ABoolF a = ABoolC {caseTrue :: a, caseFalse :: a}
    collectF = ABoolC mempty mempty
    elimF ABoolC {caseTrue, caseFalse} self b = case b of
        True_ -> caseTrue
        False_ -> caseFalse

instance ShowFoldCy ABoolF where
    showF = ABoolC {caseTrue="True", caseFalse="False"}

headIsA' = CStringC {
        caseA = const $ D True_,
        caseB = const $ D False_,
        caseEps = D False_,
        caseOr = error "TODO" -- TODO
    }

isAA' = CStringC {
        caseA = \(v,w) -> (fold headIsA' w, D $ A w),
        caseB = \(v,w) -> (v, D $ B w),
        caseEps = (D False_, D $ Eps),
        caseOr = \(v1,w1) (v2,w2) -> (error "TODO", D $ Or w1 w2) -- TODO
    }

isAA = fst . fold2 isAA'

main = do
    putStrLn $ showCy inf12
    putStrLn $ showCy inf23
    putStrLn $ showCy $ tailIL inf12
    putStrLn $ showCy $ tailIL inf23
    putStrLn $ showCy $ isAA (D $ A $ Cy $ D $ A $ D $ B $ Var 0)
    putStrLn $ showCy $ isAA (D $ A $ Cy $ D $ B $ D $ B $ Var 0)
    putStrLn $ showCy $ isAA (Cy $ D $ A $ Var 0) -- cy(x0. True) -- cleaning not working??
    putStrLn $ showCy $ isAA (D $ A $ Cy $ D $ B $ Cy $ D $ A $ Var 0) -- False -- wrong!

-- *Main> main
-- cy(x0. Cons(1,Cons(2,x0)))
-- cy(x0. Cons(2,Cons(3,x0)))
-- Cons(2,cy(x0. Cons(1,Cons(2,x0))))
-- Cons(3,cy(x0. Cons(2,Cons(3,x0))))
-- True
-- False
-- cy(x0. True)
-- False
