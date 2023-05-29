\section{Topological Preliminaries}\label{sec:Preliminaries}

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}

module Topology where

import Data.Set (Set, cartesianProduct, elemAt, intersection, isSubsetOf, union, unions, (\\), singleton)
import qualified Data.Set as S

import Test.QuickCheck
    ( Arbitrary(arbitrary), Gen, listOf1, elements, oneof, sublistOf, suchThat )

\end{code}

This section describes some topological preliminaries which will be necessary
for defining Topo Models later on. The definitions are taken from the course slides of
Topology, Logic, Learning given by Alexandru Baltag in Spring 2023. 

A \emph{topological space} is a pair $(X, \tau)$ where $X$ is a nonempty set 
and $\tau \subseteq \mathcal{P}(X)$ is a family of subsets of $X$ such that
1. $\emptyset \in \tau$ and $X \in \tau$
2. $\tau$ is closed under finite intersection: if $U, V \in \tau$ then $U \cap V \in \tau$
3. $\tau$ is closed under arbitrary unions: for any subset $A \subseteq \tau$, the union
   $\bigcup A \in \tau$

Thus, let us first define closure under intersection and closure under unions.

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

Some examples of applying the closure functions:

\begin{showCode}
ghci> (s0 :: Set Int) = S.fromList [1] 
ghci> (s1 :: Set Int) = S.fromList [2] 
ghci> (s2 :: Set Int) = S.fromList [3, 4] 
ghci> (s3 :: Set Int) = S.fromList [1, 2, 3] 
ghci> (s4 :: Set Int) = S.fromList [2, 3]
ghci> (s5 :: Set Int) = S.fromList [3, 4]
ghci> (s6 :: Set Int) = S.fromList [1, 2]
ghci> (s7 :: Set Int) = S.fromList [1, 3]
\end{showCode}

\begin{showCode}

ghci> closeUnderUnion \$ S.fromList [s0, s1, s2]
fromList [fromList [1],fromList [1,2],fromList [1,2,3,4],fromList [1,3,4],fromList [2],fromList [2,3,4],fromList [3,4]]

ghci> closeUnderIntersection \$ S.fromList [s0, s1, s2]
fromList [fromList [],fromList [1],fromList [2],fromList [3,4]]

ghci> closeUnderUnion \$ S.fromList [s3, s4, s5]
fromList [fromList [1,2,3],fromList [1,2,3,4],fromList [2,3],fromList [2,3,4],fromList [3,4]]

ghci> closeUnderIntersection \$ S.fromList [s3, s4, s5]
fromList [fromList [1,2,3],fromList [2,3],fromList [3],fromList [3,4]]

ghci> topology = (closeUnderUnion . closeUnderIntersection) \$ S.fromList [s5, s6, s7]
ghci> topology
fromList [fromList [],fromList [1],fromList [1,2],fromList [1,2,3],fromList [1,2,3,4],fromList [1,3],fromList [1,3,4],fromList [3],fromList [3,4]]

\end{showCode}

We can define a Topological space in Haskell.

\begin{code}
data TopoSpace a = TopoSpace (Set a) (Set (Set a))
    deriving (Eq, Show)
\end{code}

Now, let us implement an instance for \texttt{Arbitrary} for it. To do so, we will reimplement
some functions from `QuickCheck` for Sets.

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

isOfSizeAtMost :: Set a -> Int -> Bool
isOfSizeAtMost set s = S.size set <= s

instance (Arbitrary a, Ord a) => Arbitrary (TopoSpace a) where
  arbitrary = do
    (x'::Set a) <- arbitrary `suchThat` (`isOfSizeAtMost` 10)
    (randElem:: a) <- arbitrary
    -- Make sure x is not empty, otherwise we get an error because of `setElements`
    let x = x' `S.union` S.singleton randElem
    -- Put an artificial bound on the size of the set, otherwise it takes too long to "fix" the topology
    subbasis <- let basis = setOf1 (setElements x) `suchThat` (`isOfSizeAtMost` 3)
                  in setOf1 basis `suchThat` (`isOfSizeAtMost` 3)
    let someTopoSpace = TopoSpace x subbasis
    return (fixTopoSpace someTopoSpace)
\end{code}

Let's implement some convenience functions. The first one simply checks if the input \texttt{TopoSpace} 
object respects all the topology axioms. The second one will fixed any given (potentially broken) \texttt{TopoSpace}
to have the necessary axioms.

\begin{code}
isTopoSpace :: (Ord a) => TopoSpace a -> Bool
isTopoSpace (TopoSpace sp topo) | S.empty `notElem` topo = False
                                | sp `notElem` topo = False
                                | not (unions topo `isSubsetOf` sp) = False
                                | otherwise = topo == (closeUnderUnion . closeUnderIntersection $ topo)

fixTopoSpace :: (Ord a) => TopoSpace a -> TopoSpace a
fixTopoSpace (TopoSpace sp topo) 
  | S.empty `notElem` topo = fixTopoSpace (TopoSpace sp (topo `union` S.singleton S.empty))
  | sp `notElem` topo = fixTopoSpace (TopoSpace sp (topo `union` singleton sp))
  -- Throw an error since we don't know how the topology should look like
  | not (unions topo `isSubsetOf` sp) = error "topology not a subset of the powerset of the space"
  | otherwise = let verifTopo = closeUnderUnion . closeUnderIntersection $ topo
                in TopoSpace sp verifTopo
\end{code}

Examples of using the above:
\begin{showCode}
ghci> isTopoSpace (TopoSpace (arbUnion \$ S.fromList [s5, s6, s7]) topology)
ghci> True

ghci> badTS = TopoSpace (S.fromList [1,2,3]) (S.fromList [S.fromList [1,2], S.fromList[2,3]])
ghci> isTopoSpace badTS
ghci> False

ghci> goodTS = fixTopoSpace badTS
ghci> isTopoSpace goodTS
ghci> True

ghci> isTopoSpace (fixTopoSpace goodTS)
ghci> True

ghci> fixTopoSpace (TopoSpace (S.fromList [1,2,3,4,5]) topology)
ghci> error "topology not a subset of the powerset of the space"
\end{showCode}

The elements of $\tau$ are called \textit{open sets} or \textit{opens}.
A set $C \subseteq X$ is called a \textit{closed set} if it is the complement
of an open set, i.e., it is of the form $X \setminus U$ for some $U \in \tau$.

We let $\overline{\tau} = \{X \setminus U | U \in \tau \}$ denote the family of all
closed sets of $(X, \tau)$.

A set $A \subseteq X$ is called \textit{clopen} if it is both closed and open.

\begin{code}

openNbds :: (Eq a) => a -> TopoSpace a -> Set (Set a)
openNbds x (TopoSpace _ opens) = S.filter (x `elem`) opens

closeds :: (Ord a) => TopoSpace a -> Set (Set a)
closeds (TopoSpace space opens) = S.map (space \\) opens

isOpenIn :: (Eq a) => Set a -> TopoSpace a -> Bool
isOpenIn set (TopoSpace _ opens) = set `elem` opens

isClosedIn :: (Eq a, Ord a) => Set a -> TopoSpace a -> Bool
isClosedIn set topoSpace = set `elem` closeds topoSpace

isClopenIn :: (Eq a, Ord a) => Set a -> TopoSpace a -> Bool
isClopenIn set topoSpace = set `isOpenIn` topoSpace && set `isClosedIn` topoSpace

\end{code}

Examples of using the above:

\begin{showCode}

ghci> topoSpace = TopoSpace (S.fromList [1, 2, 3, 4]) topology

ghci> closeds topoSpace
fromList [fromList [],fromList [1,2],fromList [1,2,3,4],fromList [1,2,4],fromList [2],fromList [2,3,4],fromList [2,4],fromList [3,4],fromList [4]]

ghci> openNbds 2 topoSpace
fromList [fromList [1,2],fromList [1,2,3],fromList [1,2,3,4]]

ghci> S.fromList [1] `isOpenIn` topoSpace
True
ghci> S.fromList [1] `isClosedIn` topoSpace
False
ghci> S.fromList [] `isClopenIn` topoSpace
True

\end{showCode}

The \textit{interior} of a subset $S$ of a topological space $X$
is the union of all open subsets of $S$.

The \textit{closure} of a subset $S$ of a topological space $X$
is the intersection of all closed subsets containing $S$. 

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

interior :: (Ord a) => Set a -> TopoSpace a -> Set a
interior set topoSpace = arbUnion opensBelowSet
  where
    TopoSpace _ opens = topoSpace
    opensBelowSet = S.filter (`isSubsetOf` set) opens

closure :: (Ord a) => Set a -> TopoSpace a -> Set a
closure set topoSpace = arbIntersection closedsAboveSet
  where
    closedsAboveSet = S.filter (set `isSubsetOf`) (closeds topoSpace)

\end{code}

Examples of using the above:

\begin{showCode}

ghci> interior (S.fromList [1]) topoSpace
fromList [1]

ghci> closure (S.fromList [1]) topoSpace
fromList [1,2]

\end{showCode}
