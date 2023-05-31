\section{SetTheory}\label{sec:SetTheory}



\begin{code}

module SetTheory where

import Data.Set (Set, cartesianProduct, intersection, member, union)
import Data.Set qualified as S

import Test.QuickCheck (Arbitrary, Gen, elements, listOf1, oneof, sublistOf)

\end{code}

% Stuff for working with set algebras

\begin{code}

onceCloseUnderUnion :: (Ord a) => Set (Set a) -> Set (Set a)
onceCloseUnderUnion sets = S.map (uncurry union) (cartesianProduct sets sets)

onceCloseUnderIntersection :: (Ord a) => Set (Set a) -> Set (Set a)
onceCloseUnderIntersection sets = S.map (uncurry intersection) (cartesianProduct sets sets)

-- The closure definitions defined below are finite, but it is sufficient for our purposes
-- since we will only work with finite models.

closeUnderUnion :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderUnion sets = do
    let oneUp = onceCloseUnderUnion sets
    if sets == oneUp
        then sets
        else closeUnderUnion oneUp

closeUnderIntersection :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderIntersection sets = do
    let oneUp = onceCloseUnderIntersection sets
    if sets == oneUp
        then sets
        else closeUnderIntersection oneUp

\end{code}

% TODO - Stuff for working with relations

\begin{code}

type Relation a = Set (a, a)

field :: (Ord a) => Relation a -> Set a
field relation = domain `union` range
  where
    domain = S.map fst relation
    range = S.map snd relation

imageIn :: (Ord a) => a -> Relation a -> Set a
imageIn element relation = S.map snd $ S.filter (\(x, _) -> x == element) relation

onceMakeTransitive :: (Ord a) => Relation a -> Relation a
onceMakeTransitive relation = do
    let relField = field relation
    let fieldCubed = cartesianProduct (cartesianProduct relField relField) relField
    let relTriples = S.filter (\((x, y), z) -> (x, y) `member` relation && (y, z) `member` relation) fieldCubed
    let additions = S.map (\((x, _), z) -> (x, z)) relTriples
    relation `union` additions

makeTransitive :: (Ord a) => Relation a -> Relation a
makeTransitive relation = do
    let oneUp = onceMakeTransitive relation
    if relation == oneUp
        then relation
        else makeTransitive oneUp

\end{code}

% TODO - Stuff for testing sets

\begin{code}

-- Inspired by https://stackoverflow.com/a/35529208

setOneOf :: Set (Gen a) -> Gen a
setOneOf = oneof . S.toList

subsetOf :: (Arbitrary a, Ord a) =>  Set a -> Gen (Set a)
subsetOf =  fmap S.fromList . sublistOf .  S.toList

setOf1 :: (Arbitrary a, Ord a) => Gen a -> Gen (Set a)
setOf1 = fmap S.fromList . listOf1

setElements :: Set a -> Gen a
setElements = elements . S.toList

isOfSizeBetween :: Set a -> Int -> Int -> Bool
isOfSizeBetween set lower upper = lower <= S.size set && S.size set <= upper

\end{code}