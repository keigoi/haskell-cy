{-# LANGUAGE DeriveFunctor #-}

{-
A failed attempt to write determinisation algorithm for nondeterministic automata using cy.
Determinisation in a tree-traversal style seems to require
a non-catamorphism style recursion (at least, in a first-order system).
-}

module Aut where

import Cy
import Data.Maybe (fromMaybe)

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


type Label = String
data RoseTree = Tree Label [RoseTree] deriving Show

cataRose :: (Label -> [a] -> a) -> RoseTree -> a
cataRose f (Tree c ts) = f c (map (cataRose f) ts)

-- original (bit modified)
levels (Tree c ts) = [c] : foldr (levelwiseConcat . levels) [] ts

-- auxiliary
levelwiseConcat :: [[a]] -> [[a]] -> [[a]]
levelwiseConcat (x:xs) (y:ys) = (x ++ y) : levelwiseConcat xs ys
levelwiseConcat xs [] = xs
levelwiseConcat [] ys = ys

-- alg for levels by (rose) list folding
levelsC :: Label -> [(Label, [[Label]])] -> (Label, [[Label]])
levelsC c cont = (c, map fst cont : foldr (levelwiseConcat . snd) [] cont)

levelsCata :: RoseTree -> [[Label]]
levelsCata t = let (hd,tl) = cataRose levelsC t in [hd] : tl

headNeq :: Label -> RoseTree -> Bool
headNeq c1 (Tree c2 _) = c1 /= c2

splitHead :: RoseTree -> (Label, [RoseTree])
splitHead (Tree c t) = (c,t)

mergeTreeFun :: RoseTree -> [RoseTree] -> [RoseTree]
mergeTreeFun (Tree c1 t1) accum =
    let mfound = lookup c1 (map splitHead accum) in
    maybe
        (Tree c1 t1 : accum) -- not found: add it
        (\t2 -> Tree c1 (t1 ++ t2) : filter (headNeq c1) accum) -- concat the subtree for later merging
        mfound

mergeTrees :: [RoseTree] -> [RoseTree]
mergeTrees heads =
    let okHeads = foldr mergeTreeFun [] heads in
    map (\(Tree c t) -> Tree c (mergeTrees t)) okHeads

extree1 :: [RoseTree]
extree1 =
    [
        Tree "a" [Tree "b" []],
        Tree "a" [Tree "b" [Tree "c" []]],
        Tree "e" []
    ]

data Cofree f a = a :< f (Cofree f a)

data BinTree a = Leaf
                  | Node (BinTree a) a (BinTree a)
                  deriving (Eq, Ord, Show)

foldLT :: (b -> a -> b) -> b -> BinTree a -> b
foldLT _ e Leaf = e
foldLT f e (Node l x r) = foldLT f (f (foldLT f e l) x) r



-- cata using AutF
cataAutS f (TransS c aut) = f (c :-> cataAutS f aut)
cataAutS f DeadS = f Dead
cataAutS f (ChoiceS aut1 aut2) = f (cataAutS f aut1 :++: cataAutS f aut2)

-- exercise
flattenAutHeadSCata :: AutF ([(Char, AutSpec)], AutSpec) -> ([(Char, AutSpec)], AutSpec)
flattenAutHeadSCata (c :-> (_, aut)) = ([(c, aut)], TransS c aut)
flattenAutHeadSCata Dead = ([], DeadS)
flattenAutHeadSCata ((s1, aut1) :++: (s2, aut2)) = (s1 ++ s2, ChoiceS aut1 aut2)

flattenAutHead' = fst . cataAutS flattenAutHeadSCata

ex1 :: AutSpec
ex1 =
    TransS 'a' (TransS 'b' $ TransS 'c' acceptS)
    `ChoiceS`
    TransS 'a' (TransS 'b' $ TransS 'd' acceptS)
    `ChoiceS`
    TransS 'a' (TransS 'b' $ TransS 'c' $ TransS 'x' acceptS)

data SetF a x = Elt a | Empty | Union x x deriving Functor

type CSet a = Cy (SetF a)

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

mapSetF :: (a -> b) -> SetF a (CSet b) -> CSet b
mapSetF f (Elt x) = D $ Elt $ f x
mapSetF f Empty   = D Empty
mapSetF f (Union s1 s2) = D $ Union s1 s2

filterSetF :: (a -> Bool) -> SetF a (CSet a) -> CSet a
filterSetF p (Elt x) | p x = D $ Elt x
filterSetF p (Elt _) = D Empty
filterSetF p Empty = D Empty
filterSetF p (Union s1 s2) = D $ Union s1 s2

lookupSetF :: Eq k => k -> SetF (k, v) (CSet v) -> CSet v
lookupSetF k1 (Elt (k2, v)) | k1==k2 = D $ Elt v
lookupSetF k1 (Elt _) = D Empty
lookupSetF _  Empty   = D Empty
lookupSetF _  (Union s1 s2) = D $ Union s1 s2

filterSet :: (a -> Bool) -> CSet a -> CSet a
filterSet p = foldCy (filterSetF p)

setToList :: CSet a -> [a]
setToList (Cy t) = setToList t
setToList (D (Elt e)) = [e]
setToList (D (Union s1 s2)) =  setToList s1 ++ setToList s2
setToList (D Empty) = []
setToList (Var _) = []

data AutF t =
    (:->) Char t
    | Dead
    | (:++:) t t
    deriving Functor

type CAut = Cy AutF

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


flattenAutHeadF :: AutF (CSet (Char, CAut), CAut) -> (CSet (Char, CAut), CAut)
flattenAutHeadF (c :-> (_, aut)) = (D $ Elt (c, aut), D $ c :-> aut)
flattenAutHeadF Dead = (D Empty, D Dead)
flattenAutHeadF ((s1, aut1) :++: (s2, aut2)) = (D $ Union s1 s2, D $ aut1 :++: aut2)

mergeHeadFun :: (Char, CAut) -> [(Char, [CAut])] -> [(Char, [CAut])]
mergeHeadFun (c1, aut1) accum =
    maybe
        ((c1, [aut1]):accum)
        (\aut2 -> (c1, aut1:aut2):filter ((c1/=) . fst) accum)
        (lookup c1 accum)

mergeHeads :: CAut -> [(Char, [CAut])]
mergeHeads aut = foldr mergeHeadFun [] (setToList $ fst $ foldCy2 flattenAutHeadF aut)

makeAutFromHeads :: [(Char, CAut)] -> [CAut]
makeAutFromHeads [] = [D Dead]
makeAutFromHeads heads = map (D . uncurry (:->)) heads

newtype ConstF a t = Const a deriving (Show, Functor)

instance FoldCy (ConstF a) where
    collectF _ = mempty
    elimF f self (Const a) = f (Const a)

instance Show a => ShowFoldCy (ConstF a) where
    showF = show

deCyConst (Cy f) = deCyConst f
deCyConst (D (Const c)) = c
deCyConst (Var x) = error "var encountered"

deHead :: [(Char, [CAut])] -> CAut
deHead = foldr (\(c, auts) r -> D $ D (c :-> foldr1 (\x y -> D (x :++: y)) auts) :++: r) (D Dead)


specToCy (TransS c t) = D $ c :-> specToCy t
specToCy DeadS = D Dead
specToCy (ChoiceS aut1 aut2) = D $ specToCy aut1 :++: specToCy aut2


-- detS aut =
--     let heads = mergeHeadsToListS aut
--         headsDet = map (\(c,aut) -> (c,detS aut)) heads
--     in
--     makeAutFromHeadsS headsDet


-- testDet aut = do
--     putStrLn $ "automata: " ++ showCy aut
--     putStrLn $ "det> " ++ showCy (det aut)
