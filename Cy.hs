{-# LANGUAGE Rank2Types, TypeFamilies, GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor, FlexibleInstances, FlexibleContexts #-}

module Cy where

import Data.Maybe (fromMaybe)

-- An (partial) implementation of Makoto Hamana's FOLDr rewriting system on cyclic data:
-- Cyclic Datatypes modulo Bisimulation based on Second-Order Algebraic Theories
-- Logical Methods in Computer Science, November 15, 2017, Volume 13, Issue 4
-- https://doi.org/10.23638/LMCS-13(4:8)2017

-- cy (cyclic data structure), binding w/ DeBruijn index
data Cy f =
      Cy (Cy f)
    | D (f (Cy f))
    | Var Int

type Alg f a = f a -> a

class Functor f => FoldCy (f :: * -> *) where
    elimF :: Alg f a -> (t -> a) -> f t -> a
    collectF :: Monoid a => f a -> a

class FoldCy f => ShowFoldCy f where
    showF :: f String -> String

showCy' :: ShowFoldCy f => Int -> Cy f -> String
showCy' cnt (Cy f)   = "cy(x" ++ show cnt ++ ". " ++ showCy' (cnt+1) f ++ ")"
showCy' cnt (D c)    = elimF showF (showCy' cnt) c
showCy' cnt (Var n) = "x" ++ show (cnt - n - 1)

showCy :: ShowFoldCy f => Cy f -> String
showCy = showCy' 0

instance ShowFoldCy f => Show (Cy f) where
    show = showCy

-- printing de Bruijn indices directly
showCyRaw :: ShowFoldCy f => Cy f -> String
showCyRaw (Cy f)  = "cy(. " ++ showCyRaw f ++ ")"
showCyRaw (D c)   = elimF showF showCyRaw c
showCyRaw (Var n) = "Var " ++ show n

-- A unary fold
foldCy :: FoldCy f => Alg f (Cy g) -> Cy f -> Cy g
foldCy alg (Cy f)   = Cy (foldCy alg f)
foldCy alg (D y)    = elimF alg (foldCy alg) y
foldCy _    (Var v)  = Var v

shiftFVar' :: Functor f => (Int -> Int) -> Int -> Cy f -> Cy f
shiftFVar' f cnt (Cy cy)  = Cy (shiftFVar' f (cnt+1) cy)
shiftFVar' f cnt (D y)   = D (fmap (shiftFVar' f cnt) y)
shiftFVar' f cnt (Var n) = if n >= cnt then Var (f n) else Var n

shiftFVars :: Functor f => (Int -> Int) -> Cy f -> Cy f
shiftFVars f = shiftFVar' f 0

incrFVars :: Functor f => Cy f -> Cy f
incrFVars = shiftFVars (+1)

decrFVars :: Functor f => Cy f -> Cy f
decrFVars = shiftFVars (\i -> i - 1)

incrFVarPair :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incrFVarPair (cy1,cy2) = (incrFVars cy1, incrFVars cy2)

freeVars :: FoldCy f => Cy f -> [Int]
freeVars (Cy f)  = map (\x -> x - 1) $ filter (/=0) (freeVars f)
freeVars (D y)   = elimF collectF freeVars y
freeVars (Var v) = [v]

-- clean up unused bindings
cleanCy :: FoldCy f => Cy f -> Cy f
cleanCy (Cy f) = if 0 `elem` freeVars f then Cy (cleanCy f) else cleanCy $ decrFVars f
cleanCy (D y)  = D $ fmap cleanCy y
cleanCy (Var v) = Var v

data One (f :: * -> *)
data (f :: * -> *) :+ gs

infixr 3 :+


-- many-arg folding!

-- tuple of Cy's
data CyTup gs where
    One  :: Cy g -> CyTup (One g)
    (:+) :: Cy g -> CyTup gs -> CyTup (g :+ gs)

unOne :: CyTup (One g) -> Cy g
unOne (One g) = g

headTup :: CyTup (g :+ gs) -> Cy g
headTup (g :+ _) = g

tailTup :: CyTup (f :+ gs) -> CyTup gs
tailTup (_ :+ gs) = gs

lengthTup :: CyTup gs -> Int
lengthTup (One _) = 1
lengthTup (_ :+ cs) = 1 + lengthTup cs

newtype CyMany gs = CyMany ((Int -> Int) -> CyTup gs -> CyTup gs)

class FoldCyTup gs where
    bekic   :: CyMany gs -> CyTup gs
    genVars :: Int -> CyTup gs
    mapTup  :: (forall g. FoldCy g => Cy g -> Cy g) -> CyTup gs -> CyTup gs

instance (FoldCy g, FoldCyTup gs) => FoldCyTup (g :+ gs) where
    bekic (CyMany gsfun) =
        let t :+ _ = gsfun (+1) (Var 0 :+ bekic (CyMany (\shft gs -> tailTup $ gsfun (shft . (+1)) (Var (shft 0) :+ gs))))
            ss = bekic (CyMany (\shft gs -> tailTup $ gsfun shft (shiftFVars shft (Cy t) :+ gs)))
        in
        Cy t :+ ss
    genVars i = Var i :+ genVars i
    mapTup f (c :+ cs) = f c :+ mapTup f cs

instance FoldCy g => FoldCyTup (One g) where
    bekic (CyMany gfun) = One $ Cy (unOne $ gfun (+1) (One $ Var 0))
    mapTup f (One c) = One $ f c
    genVars i = One $ Var i

class ShowCyTup gs where
    showCyTup0 :: CyTup gs -> String

instance ShowFoldCy g => ShowCyTup (One g) where
    showCyTup0 (One f) = showCy f

instance (ShowFoldCy g, ShowCyTup gs) => ShowCyTup (g :+ gs) where
    showCyTup0 (g :+ gs) = showCy g ++ ", " ++ showCyTup0 gs

showCyTup :: ShowCyTup gs => CyTup gs -> [Char]
showCyTup gs = "<" ++ showCyTup0 gs ++ ">"

foldBekic :: (FoldCyTup gs, FoldCy f) => Alg f (CyTup gs) -> [CyTup gs] -> Cy f -> CyTup gs
foldBekic alg vars (Cy cy) = bekic $ CyMany (\_ var -> foldBekic alg (var:map (mapTup (shiftFVars (+ 1))) vars) cy)
foldBekic alg vars (D d)   = elimF alg (foldBekic alg vars) d
foldBekic alg vars (Var n) = vars !! n

foldCyTup :: (FoldCy f, FoldCy g, FoldCyTup gs) => Alg f (CyTup (g :+ gs)) -> Cy f -> CyTup (g :+ gs)
foldCyTup alg = mapTup cleanCy . foldBekic alg []

class ConvTup tup where
    type Conv tup
    convTup :: CyTup (Conv tup) -> tup
    unconvTup :: tup -> CyTup (Conv tup)

instance ConvTup (Cy g1, Cy g2) where
    type Conv (Cy g1, Cy g2) =  (g1 :+ One g2)
    convTup (g1 :+ One g2) = (g1, g2)
    unconvTup (g1, g2) = g1 :+ One g2

instance ConvTup (Cy g1, Cy g2, Cy g3) where
    type Conv (Cy g1, Cy g2, Cy g3) =  (g1 :+ g2 :+ One g3)
    convTup (g1 :+ g2 :+ One g3) = (g1, g2, g3)
    unconvTup (g1, g2, g3) = g1 :+ g2 :+ One g3

instance ConvTup (Cy g1, Cy g2, Cy g3, Cy g4) where
    type Conv (Cy g1, Cy g2, Cy g3, Cy g4) =  (g1 :+ g2 :+ g3 :+ One g4)
    convTup (g1 :+ g2 :+ g3 :+ One g4) = (g1, g2, g3, g4)
    unconvTup (g1, g2, g3, g4) = g1 :+ g2 :+ g3 :+ One g4

instance ConvTup (Cy g1, Cy g2, Cy g3, Cy g4, Cy g5) where
    type Conv (Cy g1, Cy g2, Cy g3, Cy g4, Cy g5) =  (g1 :+ g2 :+ g3 :+ g4 :+ One g5)
    convTup (g1 :+ g2 :+ g3 :+ g4 :+ One g5) = (g1, g2, g3, g4, g5)
    unconvTup (g1, g2, g3, g4, g5) = g1 :+ g2 :+ g3 :+ g4 :+ One g5

unconvTupCases :: (FoldCy f, ConvTup tup) => Alg f tup -> Alg f (CyTup (Conv tup))
unconvTupCases alg = unconvTup . alg . fmap convTup

foldCyMany :: (FoldCy f, ConvTup tup, FoldCyTup (Conv tup)) => Alg f tup -> Cy f -> tup
foldCyMany alg =
    let alg' = unconvTupCases alg in
    convTup . mapTup cleanCy . foldBekic alg' []

-- Cleaning up using AxBr. 

class FoldAxBr (f :: * -> *) where
    axBr :: Cy f -> Maybe (Cy f)
    brUnit :: f t

tryAxBr_ s = Just $ fromMaybe s (axBr s)

tryAxBr s = fromMaybe s (axBr s)

{-  **************
       Examples
    ************** -}

-- cyclic list
data CListF x = CCons Int x deriving Functor

instance FoldCy CListF where
    collectF (CCons _ x) = x
    elimF f self (CCons x xs) = f (CCons x $ self xs)

instance ShowFoldCy CListF where
    showF (CCons k s) = "CCons(" ++ show k ++ "," ++ s ++ ")"

inf12 :: Cy CListF
inf12 = Cy (D $ CCons 1 (D $ CCons 2 $ Var 0))

inf23 :: Cy CListF
inf23 = foldCy (\(CCons x r) -> D $ CCons (x+1) r) inf12

tailIL :: Cy CListF -> Cy CListF
tailIL = fst . foldCyMany (\(CCons k (x,y)) -> (y, D $ CCons k y))

tailIL' :: Cy CListF -> CyTup (CListF :+ CListF :+ One CListF)
tailIL' = foldCyTup (\(CCons k (_ :+ _ :+ One z)) -> z :+ z :+ One (D (CCons k z)))

tailIL2 :: Cy CListF -> Cy CListF
tailIL2 = headTup . tailIL'

data CStringF t =
    A t
    | B t
    | Eps
    | Or t t deriving Functor

instance FoldCy CStringF where
  collectF str = case str of
    A t -> t
    B t -> t
    Eps -> mempty
    Or t1 t2 -> t1 <> t2
  elimF f self cstr = case cstr of
    A s -> f (A $ self s)
    B s -> f (B $ self s)
    Eps -> f Eps
    Or s1 s2 -> f (Or (self s1) (self s2))

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
                D (Or s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVars s1 -- (11r)
                D (Or (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVars s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVars s  -- (13r)
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
    showF (A s) = "a("++s++")"
    showF (B s) = "b("++s++")"
    showF Eps = "ε"
    showF (Or s1 s2) = "("++s1++"|"++s2++")"

data ABoolF t = True_ | False_ | Or_ t t deriving Functor

instance FoldCy ABoolF where
    collectF True_ = mempty
    collectF False_ = mempty
    collectF (Or_ s1 s2) = s1 <> s2
    elimF f self b = case b of
        True_ -> f True_
        False_ -> f False_
        Or_ b1 b2 -> f (Or_ (self b1) (self b2))

instance ShowFoldCy ABoolF where
    showF True_  = "true"
    showF False_ = "false"
    showF (Or_ s1 s2) = "(" ++ s1 ++ " \\/ " ++ s2 ++ ")"

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
                D (Or_ s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVars s1 -- (11r)
                D (Or_ (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVars s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVars s  -- (13r)
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

headIsA' (A _) = D True_
headIsA' (B _) = D False_
headIsA' Eps = D False_
headIsA' (Or x y) = D $ Or_ x y

isAA' (A (v,w)) = (D $ Or_ (foldCy headIsA' w) v, D $ A w)
isAA' (B (v,w)) = (v, D $ B w)
isAA' Eps = (D False_, D Eps)
isAA' (Or (v1,w1) (v2,w2)) = (D $ Or_ v1 v2, D $ Or w1 w2)

isAA = tryAxBr . fst . foldCyMany isAA'

testIsAA cy = do
    putStrLn $ "term: " ++ showCy cy
    putStrLn $ "isAA> " ++ showCy (isAA cy)

main = do
    putStrLn $ showCy inf12
    putStrLn $ showCy inf23
    putStrLn $ showCy $ tailIL inf12
    putStrLn $ showCy $ tailIL inf23
    putStrLn $ showCy $ tailIL2 inf12
    putStrLn $ showCy $ tailIL2 inf23
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

    print $
        foldCyMany (\(CCons hd (tl1, tl2, tl3)) -> (tl2, D $ CCons hd tl1, D $ CCons hd tl2)) $ Cy (D $ CCons 1 $ D $ CCons 2 $ Var 0)

-- *Main> main
-- cy(x0. CCons(1,CCons(2,x0)))
-- cy(x0. CCons(2,CCons(3,x0)))
-- CCons(2,cy(x0. CCons(1,CCons(2,x0))))
-- CCons(3,cy(x0. CCons(2,CCons(3,x0))))
-- CCons(2,cy(x0. CCons(1,CCons(2,x0))))
-- CCons(3,cy(x0. CCons(2,CCons(3,x0))))

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

-- term: a(cy(x0. b(b(x0))))
-- isAA> false
-- term: a(b(cy(x0. a(x0))))
-- isAA> true
-- term: a((cy(x0. b(cy(x1. a(x1))))|a(ε)))
-- isAA> (true \/ true)
-- (cy(x0. CCons(2,x0)),cy(x0. CCons(1,x0)),CCons(1,CCons(2,cy(x0. CCons(2,x0)))))
