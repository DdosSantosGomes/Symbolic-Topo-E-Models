\section{Set theory}\label{sec:SetTheory}

In this section we define some set-theoretic helpers that will come in handy in the following sections. \\

\begin{code}

module SetTheory where

import Data.Set (Set, cartesianProduct, elemAt, intersection, member, union)
import Data.Set qualified as S

import Test.QuickCheck (Arbitrary, Gen, elements, listOf1, oneof, sublistOf)

\end{code}

\subsection{Unions and intersections}

A set of sets $S$ is called \emph{closed under unions} if $T, V \in S$ implies that $T \union V \in S$.
Similarly, $S$ is called \emph{closed under intersections} if $T, V \in S$ implies that $T \inter V \in S$.

The following functions close a passed set under unions and intersections. \\

\begin{code}

onceCloseUnderUnion :: (Ord a) => Set (Set a) -> Set (Set a)
onceCloseUnderUnion sets = S.map (uncurry union) (cartesianProduct sets sets)

onceCloseUnderIntersection :: (Ord a) => Set (Set a) -> Set (Set a)
onceCloseUnderIntersection sets = S.map (uncurry intersection) (cartesianProduct sets sets)

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

We also include, for convenience, the following functions which correspond to $\bigunion$ and $\biginter$ respectively. \\

\begin{code}

arbUnion :: (Ord a) => Set (Set a) -> Set a
arbUnion = S.foldr union S.empty

arbIntersection :: (Eq a, Ord a) => Set (Set a) -> Set a
arbIntersection sets
    | sets == S.empty = error "Cannot take the intersection of the empty set."
    | length sets == 1 = firstSet
    | otherwise = firstSet `intersection` arbIntersection restOfSets
  where
    firstSet = elemAt 0 sets
    restOfSets = S.drop 1 sets

\end{code}

\subsection{Relations}

Below are a couple of simple helper functions for working with binary relations. \\

\begin{code}

type Relation a = Set (a, a)

field :: (Ord a) => Relation a -> Set a
field relation = domain `union` range
  where
    domain = S.map fst relation
    range = S.map snd relation

imageIn :: (Ord a) => a -> Relation a -> Set a
imageIn element relation = S.map snd $ S.filter (\(x, _) -> x == element) relation

\end{code}

Given a set $X$ and a relation $R \sub X \times X$, we say that $R$ is \emph{transitive} if it satisfies, for all $x, y, z \in X$,
    \[xRy \text{ and } yRz \text{ implies } xRz\]

Below is a function for making a passed relation transitive. \\

\begin{code}

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

\subsection{Arbitrary set generation}

Here we define functions that are useful in the (constrained) generation of arbitrary sets.
These mirror their commonly-used \verb|List|-counterparts, but must be adapted as we work with \verb|Data.Set|.
Inspiration for this implementation was taken from \link{https://stackoverflow.com/a/35529208}{here}. \\

\begin{code}

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