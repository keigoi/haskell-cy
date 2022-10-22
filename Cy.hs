{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use second" #-}

{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use second" #-}
{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use second" #-}

{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use second" #-}
import Data.Maybe (fromMaybe, catMaybes, listToMaybe)

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

shiftFVar :: Functor f => (Int -> Int) -> Cy f -> Cy f
shiftFVar f = shiftFVar' f 0

incrFVar :: Functor f => Cy f -> Cy f
incrFVar = shiftFVar (+1)

decrFVar :: Functor f => Cy f -> Cy f
decrFVar = shiftFVar (\i -> i - 1)

incrFVarPair :: (Functor g1, Functor g2) => (Cy g1, Cy g2) -> (Cy g1, Cy g2)
incrFVarPair (cy1,cy2) = (incrFVar cy1, incrFVar cy2)

-- fold generating pair of cyclic structures, using Bekič
foldCy2' :: (FoldCy f, Functor g1, Functor g2) =>
    Alg f (Cy g1, Cy g2)
    -> [(Cy g1, Cy g2)]
    -> Cy f
    -> (Cy g1, Cy g2)
foldCy2' alg env (Cy f)  =
    -- Bekič
    let (_,s0) = foldCy2' alg ((Var 0, Var 0) : map incrFVarPair env) f
        (t,_)  = foldCy2' alg ((Var 0, Cy s0) : map incrFVarPair env) f
        (_,s)  = foldCy2' alg ((Cy t, Var 0) : map incrFVarPair env) f
    in (Cy t, Cy s)
foldCy2' alg env (D y)   = elimF alg (foldCy2' alg env) y
foldCy2' _   env (Var n)
    | n < length env - 1 = (Var n, Var n) -- bound variable
    | length env - 1 <= n && n < length env * 2 - 1
                         = env !! (n - length env + 1) -- free variable - looking up the env
    | otherwise          = error "fold2: impossible - unbound recursion var"

foldCy2 :: (FoldCy f, FoldCy g1, FoldCy g2) => Alg f (Cy g1, Cy g2) -> Cy f -> (Cy g1, Cy g2)
foldCy2 alg cy = let (x,y) = foldCy2' alg [] cy in (clean0 x, clean0 y)

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

type ElimCyF f t = (Cy f -> t) -> f (Cy f) -> t

class FoldCyTup gs where
    mapTup  :: (forall g. FoldCy g => Cy g -> Cy g) -> CyTup gs -> CyTup gs
    genVars :: Int -> CyTup gs
    genCys  :: CyTup gs -> CyTup gs
    incrFVarTup :: CyTup gs -> CyTup gs
    -- the many-arg fold
    foldCyTup' :: ElimCyF f (CyTup gs) -> [CyTup gs] -> Cy f -> CyTup gs

lookupVars :: FoldCyTup gs => [CyTup gs] -> Int -> CyTup gs
lookupVars vars n
    | n < length vars - 1 = genVars n
    | length vars - 1 <= n && n < length vars * 2 - 1
                          = vars !! (n - length vars + 1)
    | otherwise           = error "lookupVars: impossible - unbound recursion var"

instance FoldCy g => FoldCyTup (One g) where
    mapTup f (One c) = One $ f c
    genVars i = One $ Var i
    genCys (One g) = One $ Cy g
    incrFVarTup (One cy) = One $ incrFVar cy
    foldCyTup' elimFTup vars (Cy f)   = One $ Cy (unOne $ foldCyTup' elimFTup vars f)
    foldCyTup' elimFTup vars (D y)    = elimFTup (foldCyTup' elimFTup vars) y
    foldCyTup' _        vars (Var v)  = lookupVars vars v

tie :: Cy g -> ElimCyF f (CyTup (g :+ gs)) -> ElimCyF f (CyTup gs)
tie g elimFTup f2gs fcyf =
    tailTup $ elimFTup (\cyf -> g :+ f2gs cyf) fcyf

instance (FoldCy g, FoldCyTup gs) => FoldCyTup (g :+ gs) where
    mapTup f ((:+) c cs) = (:+) (f c) (mapTup f cs)
    genVars i = (:+) (Var i) (genVars i)
    genCys ((:+) c cs) = (:+) (Cy c) (genCys cs)
    incrFVarTup ((:+) cy1 cys) = (:+) (incrFVar cy1) (mapTup incrFVar cys)
    foldCyTup' elimTup vars (Cy f)  =
        -- many-arg Bekič!
        let vars' = map incrFVarTup vars
            (_ :+ ss0) = foldCyTup' elimTup ((Var 0 :+ genVars 0) : vars') f
            (t :+ _)   = foldCyTup' elimTup ((Var 0 :+ genCys ss0) : vars') f
            -- and decomposing the rest of the tuple, recursively
            ss  = foldCyTup' (tie t elimTup) (genVars 0 : map (tailTup . incrFVarTup) vars) f
        in Cy t :+ genCys ss
    foldCyTup' elimTup vars (D y)   =  elimTup (foldCyTup' elimTup vars) y
    foldCyTup' _       vars (Var v) = lookupVars vars v

foldCyTup :: (FoldCy f, FoldCy g, FoldCyTup gs) => Alg f (CyTup (g :+ gs)) -> Cy f -> CyTup (g :+ gs)
foldCyTup alg = mapTup clean0 . foldCyTup' (elimF alg) []

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

convTupCases :: ConvTup tup => ElimCyF f (CyTup (Conv tup)) -> ElimCyF f tup
convTupCases elimF self cyf = convTup $ elimF (unconvTup . self) cyf

unconvTupCases :: ConvTup tup => ElimCyF f tup -> ElimCyF f (CyTup (Conv tup))
unconvTupCases elimF self cyf = unconvTup $ elimF (convTup . self) cyf

foldCyMany :: (FoldCy f, ConvTup tup, FoldCyTup (Conv tup)) => Alg f tup -> Cy f -> tup
foldCyMany alg =
    let elim = unconvTupCases (elimF alg) in
    convTup . mapTup clean0 . foldCyTup' elim []

freeVars :: FoldCy f => Cy f -> [Int]
freeVars (Cy f)  = filter (/=0) (freeVars f)
freeVars (D y)   = elimF collectF freeVars y
freeVars (Var v) = [v]

-- clean up unused bindings
clean0 :: FoldCy f => Cy f -> Cy f
clean0 (Cy f) = if 0 `elem` freeVars f then Cy f else decrFVar f
clean0 (D y)  = D $ fmap clean0 y
clean0 (Var v) = Var v


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
tailIL = fst . foldCy2 (\(CCons k (x,y)) -> (y, D $ CCons k y))

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

headIsA' (A _) = D $ True_
headIsA' (B _) = D $ False_
headIsA' Eps = D False_
headIsA' (Or x y) = D $ Or_ x y

isAA' (A (v,w)) = (D $ Or_ (foldCy headIsA' w) v, D $ A w)
isAA' (B (v,w)) = (v, D $ B w)
isAA' Eps = (D False_, D Eps)
isAA' (Or (v1,w1) (v2,w2)) = (D $ Or_ v1 v2, D $ Or w1 w2)

isAA = tryAxBr . fst . foldCy2 isAA'

testIsAA cy = do
    putStrLn $ "term: " ++ showCy cy
    putStrLn $ "isAA> " ++ showCy (isAA cy)

{- 
   Additional test-bed which directly encode finite-state automata using cy.
   We are trying to 'determinise' the automata there ...
-}

-- specification (acyclic)
data AutSpec =
    TransS Char AutSpec
    | DeadS
    | ChoiceS AutSpec AutSpec
    deriving Show

-- acceptance is a special transition with symbol '!'
acceptS :: AutSpec
acceptS = TransS '!' DeadS

flattenAutHeadS :: AutSpec -> [(Char, AutSpec)]
flattenAutHeadS (TransS c aut) = [(c, aut)]
flattenAutHeadS DeadS = []
flattenAutHeadS (ChoiceS aut1 aut2) = flattenAutHeadS aut1 ++ flattenAutHeadS aut2

mergeHeadFunS :: (Char, AutSpec) -> [(Char, AutSpec)] -> [(Char, AutSpec)]
mergeHeadFunS (c1, aut1) accum =
    maybe
        ((c1, aut1):accum)
        (\aut2 -> (c1, ChoiceS aut1 aut2):filter ((c1/=) . fst) accum)
        (lookup c1 accum)

mergeHeadsToListS :: AutSpec -> [(Char, AutSpec)]
mergeHeadsToListS aut = foldr mergeHeadFunS [] (flattenAutHeadS aut)

makeAutFromHeadsS :: [(Char, AutSpec)] -> AutSpec
makeAutFromHeadsS [] = DeadS
makeAutFromHeadsS heads = foldr1 ChoiceS (map (uncurry TransS) heads)

detS aut =
    let heads = mergeHeadsToListS aut
        headsDet = map (\(c,aut) -> (c,detS aut)) heads
    in
    makeAutFromHeadsS headsDet


data SetF a x = Elt a | Empty | Union x x deriving Functor

instance FoldCy (SetF a) where
    collectF (Elt _) = mempty
    collectF Empty = mempty
    collectF (Union x y) = x <> y
    elimF f self (Elt x)    = f (Elt x)
    elimF f self Empty            = f Empty
    elimF f self (Union xs ys) = f (Union (self xs) (self ys))

instance Show a => ShowFoldCy (SetF a) where
    showF (Elt k) = show k
    showF Empty = "∅"
    showF (Union xs ys) = "(" ++ xs ++ ") U (" ++ ys ++ ")"

-- FIXME
instance FoldAxBr (SetF a) where
    brUnit = Empty
    axBr (Cy f) = do
        case axBr f of
            Just cy ->
                Just $ fromMaybe (Cy f) (fvarRules cy)
            Nothing -> fvarRules f
      where
        fvarRules cy =
            case cy of
                D (Union s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (11r)
                D (Union (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVar s  -- (13r)
                Var 0 -> return $ D brUnit -- (14r)
                _ -> Nothing
    axBr (D (Union s1 (D Empty))) = tryAxBr_ s1
    axBr (D (Union (D Empty) s2)) = tryAxBr_ s2
    axBr (D (Union s1 s2)) = do
        case (axBr s1, axBr s2) of
            (Nothing, Nothing) -> Nothing
            (Just s1, Just s2) -> tryAxBr_ $ D $ Union s1 s2
            (Nothing, Just s2) -> tryAxBr_ $ D $ Union s1 s2
            (Just s1, Nothing) -> tryAxBr_ $ D $ Union s1 s2
    axBr _ = Nothing


ex1 =
    TransS 'a' (TransS 'b' $ TransS 'c' acceptS)
    `ChoiceS`
    TransS 'a' (TransS 'b' $ TransS 'd' acceptS)
    `ChoiceS`
    TransS 'a' (TransS 'b' $ TransS 'c' $ TransS 'x' acceptS)

mapSetF :: (a -> b) -> SetF a (Cy (SetF b)) -> Cy (SetF b)
mapSetF f (Elt x) = D $ Elt $ f x
mapSetF f Empty   = D Empty
mapSetF f (Union s1 s2) = D $ Union s1 s2

filterSetF :: (a -> Bool) -> SetF a (Cy (SetF a)) -> Cy (SetF a)
filterSetF p (Elt x) | p x = D $ Elt x
filterSetF p (Elt _) = D Empty
filterSetF p Empty = D Empty
filterSetF p (Union s1 s2) = D $ Union s1 s2

lookupSetF :: Eq k => k -> SetF (k, v) (Cy (SetF v)) -> Cy (SetF v)
lookupSetF k1 (Elt (k2, v)) | k1==k2 = D $ Elt v
lookupSetF k1 (Elt _) = D Empty
lookupSetF _  Empty   = D Empty
lookupSetF _  (Union s1 s2) = D $ Union s1 s2

headSet :: Cy (SetF a) -> Maybe a
headSet (Cy t) = headSet t
headSet (D (Elt e)) = Just e
headSet (D (Union s1 s2)) = listToMaybe $ catMaybes [headSet s1, headSet s2]
headSet (D Empty) = Nothing
headSet (Var _) = Nothing

lookupSet :: Eq k => k -> Cy (SetF (k, a)) -> Maybe a
lookupSet k1 set = headSet $ foldCy (lookupSetF k1) set

filterSet :: (a -> Bool) -> Cy (SetF a) -> Cy (SetF a)
filterSet p = foldCy (filterSetF p)

-- mergeHeadFunS :: (Char, AutSpec) -> [(Char, AutSpec)] -> [(Char, AutSpec)]
-- mergeHeadFunS (c1, aut1) accum =
--     maybe
--         ((c1, aut1):accum)
--         (\aut2 -> (c1, ChoiceS aut1 aut2):filter ((c1/=) . fst) accum)
--         (lookup c1 accum)

{-
    Automata, using cy!
-}

data AutF t =
    (:->) Char t
    | Dead
    | (:++:) t t
    deriving Functor

infixr 3 :->

instance FoldCy AutF where
    collectF (_ :-> s) = s
    collectF Dead = mempty
    collectF (s1 :++: s2) = s1 <> s2
    elimF f self aut =
        case aut of
            c :-> t -> f (c :-> self t)
            Dead -> f Dead
            t1 :++: t2 -> f (self t1 :++: self t2)

instance ShowFoldCy AutF where
    showF (c :-> t) = "-" ++ [c] ++ "->" ++ t
    showF Dead = "0"
    showF (t1 :++: t2) = "(" ++ t1 ++ " ++ " ++ t2 ++ ")"

instance FoldAxBr AutF where
    brUnit = Dead
    axBr (Cy f) = do
        case axBr f of
            Just cy ->
                Just $ fromMaybe (Cy f) (fvarRules cy)
            Nothing -> fvarRules f
      where
        fvarRules cy =
            case cy of
                D (s1 :++: Var 0) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (11r)
                D (Var 0 :++: s1) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVar s  -- (13r)
                Var 0 -> return $ D brUnit -- (14r)
                _ -> Nothing
    axBr (D (s1 :++: D Dead)) = tryAxBr_ s1
    axBr (D (D Dead :++: s2)) = tryAxBr_ s2
    axBr (D (s1 :++: s2)) = do
        case (axBr s1, axBr s2) of
            (Nothing, Nothing) -> Nothing
            (Just s1, Just s2) -> tryAxBr_ $ D $ s1 :++: s2
            (Nothing, Just s2) -> tryAxBr_ $ D $ s1 :++: s2
            (Just s1, Nothing) -> tryAxBr_ $ D $ s1 :++: s2
    axBr _ = Nothing


flattenAutHeadF (_, c :-> aut) = (D $ Elt (c, aut), D $ c :-> aut)
flattenAutHeadF (_, Dead) = (D Empty, D Dead)
flattenAutHeadF (s1 :++: s2, aut1 :++: aut2) = (D $ Union s1 s2, D $ aut1 :++: aut2)


{-
    A (currently-failing attempt of) determinisation algorithm using fold on cy.
-}

-- mergeTransC :: Char -> Cy AutF -> Cases AutF (Cy AutF, Cy AutF)
-- mergeTransC c1 aut1 = AutC {
--     caseTrans = \c2 (_, t) ->
--         (if c1==c2 then
--             D $ c1 :-> merge aut1 t
--         else
--             -- merging two edges into one, continue to determinise the following states?
--             -- the main problem here is a thoughtless use of mutual recursion
--             -- which must also be eliminated by using fold.
--             D $ D (c1 :-> {-det-} aut1) :++: D (c2 :-> {-det-} t),
--         D (c2 :-> t)),
--     caseAccept =
--         (D $ D (c1 :-> aut1) :++: D Accept, D Accept),
--     caseDead =
--         (D $ c1 :-> aut1, D Dead),
--     caseChoice = \(_,t) (_,s) ->
--         (merge (mergeTrans c1 aut1 t) (mergeTrans c1 aut1 s), D $ t :++: s)
-- }

-- mergeTrans c1 aut1 aut2 = fst $ foldCy2 (mergeTransC c1 aut1) aut2


-- merge aut1 aut2 = fst $ foldCy2 (mergeC aut2) aut1

-- mergeC :: Cy AutF -> Cases AutF (Cy AutF, Cy AutF)
-- mergeC aut2 = AutC {
--     caseTrans = \c (_, t) ->
--         (fst $ foldCy2 (mergeTransC c t) aut2, D (c :-> t)),
--     caseAccept =
--         (D $ D Accept :++: aut2, D Accept),
--     caseDead =
--         (aut2, D Dead),
--     caseChoice = \(_,t) (_,s) ->
--         (merge (merge t aut2) (merge s aut2) , D $ t :++: s)
-- }

-- detC :: Cases AutF (Cy AutF, Cy AutF)
-- detC = AutC {
--         caseTrans = \c (_, t) ->
--             (D (c :-> t), D (c :-> t)),
--         caseAccept =
--             (D Accept, D Accept),
--         caseDead =
--             (D Dead, D Dead),
--         caseChoice = \(_,t) (_,s) ->
--             (fst $ foldCy2 (mergeC s) t, D $ t :++: s)
--     }

-- det = fst . foldCy2 detC

-- testDet aut = do
--     putStrLn $ "automata: " ++ showCy aut
--     putStrLn $ "det> " ++ showCy (det aut)


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
    putStrLn ""

    -- automata examples (ongoing, does not work properly yet)
    -- testDet $ Cy $ D (D ('a' :-> D ('b' :-> D ('a' :-> Var 0))) :++: D ('a' :-> D ('b' :-> D ('c' :-> D Accept))))
    -- testDet $ Cy $ D (D ('a' :-> D ('b' :-> Var 0)) :++: D ('a' :-> D ('c' :-> D Accept)))
    -- testDet $ D (D ('a' :-> Cy (D ('b' :-> Var 0))) :++: D ('a' :-> D ('c' :-> D Accept)))

-- *Main> main
-- cy(x0. Cons(1,Cons(2,x0)))
-- cy(x0. Cons(2,Cons(3,x0)))
-- Cons(2,cy(x0. Cons(1,Cons(2,x0))))
-- Cons(3,cy(x0. Cons(2,Cons(3,x0))))
-- Cons(2,cy(x0. Cons(1,Cons(2,x0))))
-- Cons(3,cy(x0. Cons(2,Cons(3,x0))))

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
-- isAA> (true \/ cy(x0. (x0 \/ x0)))
