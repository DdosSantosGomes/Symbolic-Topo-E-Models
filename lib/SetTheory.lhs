\section{SetTheory}\label{sec:SetTheory}



\begin{code}

module SetTheory where

import Data.Set (Set, cartesianProduct, intersection, member, union)
import Data.Set qualified as S

import Test.QuickCheck (Arbitrary, Gen, elements, listOf1, oneof, sublistOf)

\end{code}

% Stuff for working with set algebras

\begin{code}

unionize :: (Ord a) => Set (Set a) -> Set (Set a)
unionize sets = S.map (uncurry union) (cartesianProduct sets sets)

intersectionize :: (Ord a) => Set (Set a) -> Set (Set a)
intersectionize sets = S.map (uncurry intersection) (cartesianProduct sets sets)

-- The closure definitions defined below are finite, but it is sufficient for our purposes
-- since we will only work with finite models.

closeUnderUnion :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderUnion sets = do
    let oneUp = unionize sets
    if sets == oneUp
        then sets
        else closeUnderUnion oneUp

closeUnderIntersection :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderIntersection sets = do
    let oneUp = intersectionize sets
    if sets == oneUp
        then sets
        else closeUnderIntersection oneUp

\end{code}

% TODO - Stuff for working with relations

\begin{code}

domain :: (Ord a) => Set (a, a) -> Set a
domain = S.map fst

range :: (Ord a) => Set (a, a) -> Set a
range = S.map snd

field :: (Ord a) => Set (a, a) -> Set a
field relation = domain relation `union` range relation

imageIn :: (Ord a) => a -> Set (a, a) -> Set a
imageIn element relation = S.map snd $ S.filter (\(x, _) -> x == element) relation

transitivize :: (Ord a) => Set (a, a) -> Set (a, a)
transitivize relation = do
    let relField = field relation
    let fieldCubed = cartesianProduct (cartesianProduct relField relField) relField
    let relTriples = S.filter (\((x, y), z) -> (x, y) `member` relation && (y, z) `member` relation) fieldCubed
    let additions = S.map (\((x, _), z) -> (x, z)) relTriples
    relation `union` additions

makeTransitive :: (Ord a) => Set (a, a) -> Set (a, a)
makeTransitive relation = do
    let oneUp = transitivize relation
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