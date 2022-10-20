{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs, NamedFieldPuns #-}
import Data.Maybe (fromMaybe)

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

shiftFVar' :: Functor f => (Int -> Int) -> Int -> Cy f -> Cy f
shiftFVar' f cnt (Cy cy)  = Cy (shiftFVar' f (cnt+1) cy)
shiftFVar' f cnt (D y)   = D (fmap (shiftFVar' f cnt) y)
shiftFVar' f cnt (Var n) = if n >= cnt then Var (f n) else Var n

shiftFVar :: Functor f => (Int -> Int) -> Cy f -> Cy f
shiftFVar f = shiftFVar' f 0

incrFVar :: Functor f => Cy f -> Cy f
incrFVar = shiftFVar (+1)

decrFVar :: Functor f => Cy f -> Cy f
decrFVar = shiftFVar (\i -> i - 1)

incrFVarPair :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incrFVarPair (cy1,cy2) = (incrFVar cy1, incrFVar cy2)

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

-- A failed attempt to generalise fold2 to foldMany

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

-- tailIL' :: Cy IListF ->　CyTup (IListF :+ IListF :+: IListF) 
-- tailIL' = foldMany (IListC (\k (_ :+ (_ :+: z)) -> z :+ z :+: D (Cons k z)))

-- tailIL2 :: Cy IListF -> Cy IListF
-- tailIL2 = fstTup . tailIL'

freeVars :: FoldCy f => Cy f -> [Int]
freeVars (Cy f)  = filter (/=0) (freeVars f)
freeVars (D y)   = elimF collectF freeVars y
freeVars (Var v) = [v]

-- clean up unused bindings
clean0 :: FoldCy f => Cy f -> Cy f
clean0 (Cy f) = if 0 `elem` freeVars f then Cy f else decrFVar f
clean0 (D y)  = D $ fmap clean0 y
clean0 (Var v) = Var v

-- print w/ De Bruijn indices
showCyRaw :: FoldCy f => Cata f String -> Cy f -> String
showCyRaw cata (Cy f)  = "cy(. " ++ showCyRaw cata f ++ ")"
showCyRaw cata (D c)   = elimF cata (showCyRaw cata) c
showCyRaw _    (Var n) = "Var " ++ show n

-- infinite list
data IListF x = Cons Int x deriving Functor

instance FoldCy IListF where
    newtype Cata IListF a = IListC (Int -> a -> a)
    collectF = IListC (const id)
    elimF (IListC cata) self (Cons x xs) = cata x (self xs)

instance ShowFoldCy IListF where
    showF = IListC (\k s -> "Cons(" ++ show k ++ "," ++ s ++ ")")

inf12 :: Cy IListF
inf12 = Cy (D $ Cons 1 (D $ Cons 2 $ Var 0))

inf23 :: Cy IListF
inf23 = fold (IListC (\x r -> D $ Cons (x+1) r)) inf12

tailIL :: Cy IListF -> Cy IListF
tailIL = fst . fold2 (IListC (\k (x,y) -> (y, D $ Cons k y)))

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

class FoldAxBr (f :: * -> *) where
    axBr :: Cy f -> Maybe (Cy f)
    brUnit :: f t

tryAxBr_ s = Just $ fromMaybe s (axBr s)

tryAxBr s = fromMaybe s (axBr s)

instance FoldAxBr CStringF where
    brUnit = Eps
    axBr (Cy f) =
        case axBr f of
            Just cy -> 
                Just $ fromMaybe (Cy f) (fvarRules cy)
            Nothing -> fvarRules f
      where 
        fvarRules cy =
            case cy of
                D (Or s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (11r)
                D (Or (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVar s  -- (13r)
                Var 0 -> return $ D brUnit -- (14r)
                _ -> Nothing
    axBr (D (Or s1 (D Eps))) = tryAxBr_ s1 -- (15r)
    axBr (D (Or (D Eps) s2)) = tryAxBr_ s2 -- (16r)
    axBr (D (Or s1 s2)) = 
        case (axBr s1, axBr s2) of 
            (Nothing, Nothing) -> Nothing
            (Just s1, Just s2) -> tryAxBr_ $ D $ Or s1 s2
            (Nothing, Just s2) -> tryAxBr_ $ D $ Or s1 s2
            (Just s1, Nothing) -> tryAxBr_ $ D $ Or s1 s2
    axBr (D (A s)) = D . A <$> axBr s
    axBr (D (B s)) = D . B <$> axBr s
    axBr s = Nothing

instance ShowFoldCy CStringF where
    showF = CStringC {caseA= \s->"a("++s++")", caseB= \s -> "b("++s++")", caseEps="ε", caseOr= \s1 s2 -> "("++s1++"|"++s2++")"}

data ABoolF t = True_ | False_ | Or_ t t deriving Functor

instance FoldCy ABoolF where
    data Cata ABoolF a = ABoolC {caseTrue :: a, caseFalse :: a, caseOrB :: a -> a -> a}
    collectF = ABoolC mempty mempty (<>)
    elimF ABoolC {caseTrue, caseFalse, caseOrB} self b = case b of
        True_ -> caseTrue
        False_ -> caseFalse
        Or_ b1 b2 -> caseOrB (self b1) (self b2)

instance ShowFoldCy ABoolF where
    showF = ABoolC {caseTrue="true", caseFalse="false", caseOrB= \s1 s2 -> "(" ++ s1 ++ " \\/ " ++ s2 ++ ")"}

-- FIXME
instance FoldAxBr ABoolF where
    brUnit = False_
    axBr (Cy f) = do
        case axBr f of
            Just cy -> 
                Just $ fromMaybe (Cy f) (fvarRules cy)
            Nothing -> fvarRules f
      where 
        fvarRules cy =
            case cy of
                D (Or_ s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (11r)
                D (Or_ (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVar s  -- (13r)
                Var 0 -> return $ D brUnit -- (14r)
                _ -> Nothing
    axBr (D (Or_ s1 (D False_))) = tryAxBr_ s1
    axBr (D (Or_ (D False_) s2)) = tryAxBr_ s2
    axBr (D (Or_ s1 s2)) = do
        case (axBr s1, axBr s2) of 
            (Nothing, Nothing) -> Nothing
            (Just s1, Just s2) -> tryAxBr_ $ D $ Or_ s1 s2
            (Nothing, Just s2) -> tryAxBr_ $ D $ Or_ s1 s2
            (Just s1, Nothing) -> tryAxBr_ $ D $ Or_ s1 s2
    axBr _ = Nothing

headIsA' = CStringC {
        caseA = const $ D True_,
        caseB = const $ D False_,
        caseEps = D False_,
        caseOr = \x y -> D (Or_ x y)
    }

isAA' = CStringC {
        caseA = \(v,w) -> (D $ Or_ (fold headIsA' w) v, D $ A w),
        caseB = \(v,w) -> (v, D $ B w),
        caseEps = (D False_, D Eps),
        caseOr = \(v1,w1) (v2,w2) -> (D $ Or_ v1 v2, D $ Or w1 w2) -- TODO
    }

isAA = tryAxBr . fst . fold2 isAA'

testIsAA cy = do
    putStrLn $ "term: " ++ showCy cy
    putStrLn $ "isAA> " ++ showCy (isAA cy)


main = do
    putStrLn $ showCy inf12
    putStrLn $ showCy inf23
    putStrLn $ showCy $ tailIL inf12
    putStrLn $ showCy $ tailIL inf23
    putStrLn ""
    let a = D . A
        b = D . B
        or_ s t = D (Or s t)
        eps = D Eps
    -- examples from page 33
    testIsAA (b $ a $ a $ b eps)
    testIsAA (b $ b eps)
    testIsAA (b eps `or_` a (a eps))
    testIsAA (Cy $ a $ Var 0)
    testIsAA (b $ Cy $ a $ b $ a $ Var 0)
    putStrLn ""
    testIsAA (a $ Cy $ b $ b $ Var 0)
    testIsAA (a $ b $ Cy $ a $ Var 0)
    testIsAA (a (Cy (b $ Cy $ a $ Var 0) `or_` a eps)) -- FIXME (true \/ cy(x0. (x0 \/ x0)))

-- *Main> main
-- cy(x0. Cons(1,Cons(2,x0)))
-- cy(x0. Cons(2,Cons(3,x0)))
-- Cons(2,cy(x0. Cons(1,Cons(2,x0))))
-- Cons(3,cy(x0. Cons(2,Cons(3,x0))))
-- 
-- term: b(a(a(b(ε))))
-- isAA> true
-- term: b(b(ε))
-- isAA> false
-- term: (b(ε)|a(a(ε)))
-- isAA> true
-- term: cy(x0. a(x0))
-- isAA> true
-- term: b(cy(x0. a(b(a(x0)))))
-- isAA> true
-- 
-- term: a(cy(x0. b(b(x0))))
-- isAA> false
-- term: a(b(cy(x0. a(x0))))
-- isAA> true
-- term: a((cy(x0. b(cy(x1. a(x1))))|a(ε)))
-- isAA> (true \/ cy(x0. (x0 \/ x0)))
