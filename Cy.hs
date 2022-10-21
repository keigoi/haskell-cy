{-# LANGUAGE Rank2Types, TypeFamilies, DataKinds, DeriveFunctor, GADTs, NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
import Data.Maybe (fromMaybe)

-- An (partial) implementation of M. Hamana's FOLDr rewriting system on cyclic data:
-- Cyclic Datatypes modulo Bisimulation based on Second-Order Algebraic Theories
-- Logical Methods in Computer Science, November 15, 2017, Volume 13, Issue 4
-- https://doi.org/10.23638/LMCS-13(4:8)2017

-- cy (cyclic data structure), binding w/ DeBruijn index
data Cy f =
      Cy (Cy f)
    | D (f (Cy f))
    | Var Int

class Functor f => FoldCy (f :: * -> *) where
    data Cases f a -- case analysis on the type f t, producing a (see examples)
    collectF :: Monoid a => Cases f a
    elimF :: Cases f a -> (t -> a) -> f t -> a

class FoldCy f => ShowFoldCy f where
    showF :: Cases f String

showCy' :: ShowFoldCy f => Int -> Cy f -> String
showCy' cnt (Cy f)   = "cy(x" ++ show cnt ++ ". " ++ showCy' (cnt+1) f ++ ")"
showCy' cnt (D c)    = elimF showF (showCy' cnt) c
showCy' cnt (Var n) = "x" ++ show (cnt - n - 1)

showCy :: ShowFoldCy f => Cy f -> String
showCy = showCy' 0

-- printing de Bruijn indices directly
showCyRaw :: FoldCy f => Cases f String -> Cy f -> String
showCyRaw cata (Cy f)  = "cy(. " ++ showCyRaw cata f ++ ")"
showCyRaw cata (D c)   = elimF cata (showCyRaw cata) c
showCyRaw _    (Var n) = "Var " ++ show n

-- A unary fold
foldCy :: FoldCy f => Cases f (Cy g) -> Cy f -> Cy g
foldCy cata (Cy f)   = Cy (foldCy cata f)
foldCy cata (D y)    = elimF cata (foldCy cata) y
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
    Cases f (Cy g1, Cy g2)
    -> [(Cy g1, Cy g2)]
    -> Cy f
    -> (Cy g1, Cy g2)
foldCy2' cata env (Cy f)  =
    -- Bekič
    let (_,s0) = foldCy2' cata ((Var 0, Var 0) : map incrFVarPair env) f
        (t,_)  = foldCy2' cata ((Var 0, Cy s0) : map incrFVarPair env) f
        (_,s)  = foldCy2' cata ((Cy t, Var 0) : map incrFVarPair env) f
    in (Cy t, Cy s)
foldCy2' cata env (D y)   = elimF cata (foldCy2' cata env) y
foldCy2' _    env (Var n)
    | n < length env - 1 = (Var n, Var n) -- bound variable
    | length env - 1 <= n && n < length env * 2 - 1
                         = env !! (n - length env + 1) -- free variable - looking up the env
    | otherwise          = error "fold2: impossible - unbound recursion var"

foldCy2 :: (FoldCy f, FoldCy g1, FoldCy g2) => Cases f (Cy g1, Cy g2) -> Cy f -> (Cy g1, Cy g2)
foldCy2 cata cy = let (x,y) = foldCy2' cata [] cy in (clean0 x, clean0 y)

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

type ElimF f gs = (Cy f -> gs) -> f (Cy f) -> gs

class FoldCyTup gs where
    mapTup  :: (forall g. FoldCy g => Cy g -> Cy g) -> CyTup gs -> CyTup gs
    genVars :: Int -> CyTup gs
    genCys  :: CyTup gs -> CyTup gs
    incrFVarTup :: CyTup gs -> CyTup gs
    -- the many-arg fold
    foldCyTup' :: ElimF f (CyTup gs) -> [CyTup gs] -> Cy f -> CyTup gs

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

tie :: Cy g -> ElimF f (CyTup (g :+ gs)) -> ElimF f (CyTup gs)
tie g elimFTup f2gs fcyf =
    tailTup $ elimFTup (\cyf -> g :+ f2gs cyf) fcyf

instance (FoldCy g, FoldCyTup gs) => FoldCyTup (g :+ gs) where
    mapTup f ((:+) c cs) = (:+) (f c) (mapTup f cs)
    genVars i = (:+) (Var i) (genVars i)
    genCys ((:+) c cs) = (:+) (Cy c) (genCys cs)
    incrFVarTup ((:+) cy1 cys) = (:+) (incrFVar cy1) (mapTup incrFVar cys)
    foldCyTup' elimTup vars (Cy f)  =
        -- many-arg Bekič!
        let (_ :+ ss0) = foldCyTup' elimTup ((:+) (Var 0) (genVars 0) : map incrFVarTup vars) f
            (t :+ _)   = foldCyTup' elimTup ((:+) (Var 0) (genCys ss0) : map incrFVarTup vars) f
            -- and decomposing the rest of the tuple, recursively
            ss  = foldCyTup' (tie t elimTup) (genVars 0 : map (tailTup . incrFVarTup) vars) f
        in Cy t :+ genCys ss
    foldCyTup' elimTup vars (D y)   =  elimTup (foldCyTup' elimTup vars) y
    foldCyTup' _       vars (Var v) = lookupVars vars v

foldCyTup :: (FoldCy f, FoldCy g, FoldCyTup gs) => Cases f (CyTup (g :+ gs)) -> Cy f -> CyTup (g :+ gs)
foldCyTup cata = mapTup clean0 . foldCyTup' (elimF cata) []

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

convTupCases :: ConvTup tup => ElimF f (CyTup (Conv tup)) -> ElimF f tup
convTupCases elimF self cyf = convTup $ elimF (unconvTup . self) cyf

unconvTupCases :: ConvTup tup => ElimF f tup -> ElimF f (CyTup (Conv tup))
unconvTupCases elimF self cyf = unconvTup $ elimF (convTup . self) cyf

foldCyMany :: (FoldCy f, ConvTup tup, FoldCyTup (Conv tup)) => Cases f tup -> Cy f -> tup
foldCyMany cata = 
    let elim = unconvTupCases (elimF cata) in
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

-- infinite list
data IListF x = Cons Int x deriving Functor

instance FoldCy IListF where
    newtype Cases IListF a = IListC (Int -> a -> a)
    collectF = IListC (const id)
    elimF (IListC cata) self (Cons x xs) = cata x (self xs)

instance ShowFoldCy IListF where
    showF = IListC (\k s -> "Cons(" ++ show k ++ "," ++ s ++ ")")

inf12 :: Cy IListF
inf12 = Cy (D $ Cons 1 (D $ Cons 2 $ Var 0))

inf23 :: Cy IListF
inf23 = foldCy (IListC (\x r -> D $ Cons (x+1) r)) inf12

tailIL :: Cy IListF -> Cy IListF
tailIL = fst . foldCy2 (IListC (\k (x,y) -> (y, D $ Cons k y)))

tailIL' :: Cy IListF -> CyTup (IListF :+ IListF :+ One IListF)
tailIL' = foldCyTup (IListC (\k (_ :+ _ :+ One z) -> z :+ z :+ One (D (Cons k z))))

tailIL2 :: Cy IListF -> Cy IListF
tailIL2 = headTup . tailIL'

data CStringF t =
    A t
    | B t
    | Eps
    | Or t t deriving Functor

instance FoldCy CStringF where
  data Cases CStringF a = CStringC {caseA :: a -> a, caseB :: a -> a, caseEps :: a, caseOr :: a -> a -> a}
  collectF = CStringC id id mempty (<>)
  elimF CStringC {caseA, caseB, caseEps, caseOr} self cstr = case cstr of
    A s -> caseA (self s)
    B s -> caseB (self s)
    Eps -> caseEps
    Or s1 s2 -> caseOr (self s1) (self s2)

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
    showF = CStringC {
        caseA= \s->"a("++s++")",
        caseB= \s -> "b("++s++")",
        caseEps="ε",
        caseOr= \s1 s2 -> "("++s1++"|"++s2++")"
    }

data ABoolF t = True_ | False_ | Or_ t t deriving Functor

instance FoldCy ABoolF where
    data Cases ABoolF a = ABoolC {caseTrue :: a, caseFalse :: a, caseOrB :: a -> a -> a}
    collectF = ABoolC mempty mempty (<>)
    elimF ABoolC {caseTrue, caseFalse, caseOrB} self b = case b of
        True_ -> caseTrue
        False_ -> caseFalse
        Or_ b1 b2 -> caseOrB (self b1) (self b2)

instance ShowFoldCy ABoolF where
    showF = ABoolC {
        caseTrue="true",
        caseFalse="false",
        caseOrB= \s1 s2 -> "(" ++ s1 ++ " \\/ " ++ s2 ++ ")"
    }

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
        caseA = \(v,w) -> (D $ Or_ (foldCy headIsA' w) v, D $ A w),
        caseB = \(v,w) -> (v, D $ B w),
        caseEps = (D False_, D Eps),
        caseOr = \(v1,w1) (v2,w2) -> (D $ Or_ v1 v2, D $ Or w1 w2) -- TODO
    }

isAA = tryAxBr . fst . foldCy2 isAA'

testIsAA cy = do
    putStrLn $ "term: " ++ showCy cy
    putStrLn $ "isAA> " ++ showCy (isAA cy)


data AutF t =
    (:->) Char t
    | Accept
    | Dead
    | Choice t t
    deriving Functor

infixr 3 :->

instance FoldCy AutF where
    data Cases AutF a =
        AutC {
            caseTrans :: Char -> a -> a,
            caseAccept :: a,
            caseDead :: a,
            caseChoice :: a -> a -> a
        }
    collectF = AutC (const id) mempty mempty (<>)
    elimF AutC {caseTrans, caseAccept, caseDead, caseChoice} self aut =
        case aut of
            c :-> t -> caseTrans c $ self t
            Accept -> caseAccept
            Dead -> caseDead
            Choice t1 t2 -> caseChoice (self t1) (self t2)

instance ShowFoldCy AutF where
    showF = AutC {
        caseTrans = \c t -> "-" ++ [c] ++ "->" ++ t,
        caseAccept = "1",
        caseDead = "0",
        caseChoice = \t1 t2 -> "(" ++ t1 ++ " + " ++ t2 ++ ")"
    }

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
                D (Choice s1 (Var 0)) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (11r)
                D (Choice (Var 0) s1) | 0 `notElem` freeVars s1 -> return $ decrFVar s1 -- (12r)
                s | 0 `notElem` freeVars s -> return $ decrFVar s  -- (13r)
                Var 0 -> return $ D brUnit -- (14r)
                _ -> Nothing
    axBr (D (Choice s1 (D Dead))) = tryAxBr_ s1
    axBr (D (Choice (D Dead) s2)) = tryAxBr_ s2
    axBr (D (Choice s1 s2)) = do
        case (axBr s1, axBr s2) of
            (Nothing, Nothing) -> Nothing
            (Just s1, Just s2) -> tryAxBr_ $ D $ Choice s1 s2
            (Nothing, Just s2) -> tryAxBr_ $ D $ Choice s1 s2
            (Just s1, Nothing) -> tryAxBr_ $ D $ Choice s1 s2
    axBr _ = Nothing

data AutSpec =
    TransS Char AutSpec
    | AcceptS
    | DeadS
    | ChoiceS AutSpec AutSpec
    deriving Show

(|->) :: Char -> AutSpec -> AutSpec
(|->) = TransS

infixr 3 |->

mergeTransS :: Char -> AutSpec -> AutSpec -> AutSpec
mergeTransS c1 aut1 (TransS c2 aut2)  =
    if c1==c2 then
        TransS c1 (mergeS aut1 aut2)
    else
        ChoiceS (TransS c1 (detS aut1)) (TransS c2 (detS aut2))
mergeTransS c1 aut1 (ChoiceS aut21 aut22) = mergeS (mergeTransS c1 aut1 aut21) (mergeTransS c1 aut1 aut22)
mergeTransS c1 aut1 AcceptS = ChoiceS (TransS c1 (detS aut1)) AcceptS
mergeTransS c1 aut1 DeadS = DeadS

mergeS :: AutSpec -> AutSpec -> AutSpec
mergeS (TransS c1 aut1) aut2 = mergeTransS c1 aut1 aut2
mergeS (ChoiceS aut11 aut12) aut2 = mergeS (mergeS aut11 aut2) (mergeS aut12 aut2)
mergeS AcceptS aut2 = ChoiceS AcceptS (detS aut2)
mergeS DeadS _ = DeadS

detS :: AutSpec -> AutSpec
detS (TransS c aut) = TransS c $ detS aut
detS (ChoiceS aut1 aut2) = mergeS aut1 aut2
detS AcceptS = AcceptS
detS DeadS = DeadS

-- merge :: Cy AutF -> Cases AutF (Cy AutF, Cy AutF)
-- merge aut1 = AutC {
--     caseTrans = \c (s,t) -> (D $ c :-> s, D $ c :-> t),
--     caseAccept = (D Accept, D Accept),
--     caseDead = (D Dead, D Dead),
--     caseChoice = \(s1,t1) (s2,t2) ->
--         (D $ Choice s1 s2, D $ Choice s1 s2)
-- }

-- det :: Cases AutF (Cy AutF, Cy AutF)
-- det = AutC {
--         caseTrans = \c (u, t) ->
--             (D (c :-> u), D $ c :-> t),
--         caseAccept =
--             (D Accept, D Accept),
--         caseDead =
--             (D Dead, D Dead),
--         caseChoice = \(s1,t1) (s2,t2) ->
--             (fst (foldCy2 (merge t1) t2), D $ Choice t1 t2)
--     }


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
