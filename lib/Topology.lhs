
\section{Topological Preliminaries}\label{sec:Preliminaries}

This section describes some topological preliminaries which will be necessary
for defining Topo Models later on. The definitions are taken from the course slides of
Topology, Logic, Learning given by Alexandru Baltag in Spring 2023. 

\textit{Note: In our Haskell implementation we  will use lists instead of sets as they seem easier to work with.}

A \textit{topological space} is a pair $(X, \tau)$ where $X$ is a nonempty set 
and $\tau \subseteq \mathcal{P}(X)$ is a family of subsets of $X$ such that
1. $\emptyset \in \tau$ and $X \in \tau$
2. $\tau$ is closed under finite intersection: if $U, V \in \tau$ then $U \cap V \in \tau$
3. $\tau$ is closed under arbitrary unions: for any subset $A \subseteq \tau$, the union
   $\bigcup A \in \tau$

Thus, let us first define closure under intersection and closure under unions.

\begin{code}

module Topology where

import Data.Set (Set, cartesianProduct, elemAt, intersection, isSubsetOf, union, (\\))
import Data.Set qualified as S

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
ghci> (s0 :: Set Int) = Set.fromList [1] 
ghci> (s1 :: Set Int) = Set.fromList [2] 
ghci> (s2 :: Set Int) = Set.fromList [3, 4] 
ghci> (s3 :: Set Int) = Set.fromList [1, 2, 3] 
ghci> (s4 :: Set Int) = Set.fromList [2, 3]
ghci> (s5 :: Set Int) = Set.fromList [3, 4]
ghci> (s6 :: Set Int) = Set.fromList [1, 2]
ghci> (s7 :: Set Int) = Set.fromList [1, 3]
\end{showCode}

\begin{showCode}

ghci> closeUnderUnion \$ Set.fromList [s0, s1, s2]
fromList [fromList [1],fromList [1,2],fromList [1,2,3,4],fromList [1,3,4],fromList [2],fromList [2,3,4],fromList [3,4]]

ghci> closeUnderIntersection \$ Set.fromList [s0, s1, s2]
fromList [fromList [],fromList [1],fromList [2],fromList [3,4]]

ghci> closeUnderUnion \$ Set.fromList [s3, s4, s5]
fromList [fromList [1,2,3],fromList [1,2,3,4],fromList [2,3],fromList [2,3,4],fromList [3,4]]

ghci> closeUnderIntersection \$ Set.fromList [s3, s4, s5]
fromList [fromList [1,2,3],fromList [2,3],fromList [3],fromList [3,4]]

ghci> topology = (closeUnderUnion . closeUnderIntersection) \$ Set.fromList [s5, s6, s7]
ghci> topology
fromList [fromList [],fromList [1],fromList [1,2],fromList [1,2,3],fromList [1,2,3,4],fromList [1,3],fromList [1,3,4],fromList [3],fromList [3,4]]

\end{showCode}

Now, we can define a Topological space in Haskell.

\begin{code}
data TopoSpace a = TopoSpace (Set a) (Set (Set a))
    deriving (Eq, Show)
\end{code}

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

ghci> topoSpace = TopoSpace (Set.fromList [1, 2, 3, 4]) topology

ghci> closeds topoSpace
fromList [fromList [],fromList [1,2],fromList [1,2,3,4],fromList [1,2,4],fromList [2],fromList [2,3,4],fromList [2,4],fromList [3,4],fromList [4]]

ghci> openNbds 2 topoSpace
fromList [fromList [1,2],fromList [1,2,3],fromList [1,2,3,4]]

ghci> (Set.fromList [1]) `isOpenIn` topoSpace
True
ghci> (Set.fromList [1]) `isClosedIn` topoSpace
False
ghci> (Set.fromList []) `isClopenIn` topoSpace
True

\end{showCode}

% TODO: write tests for the topology axioms

% TODO: subbasis and basis?

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

ghci> interior (Set.fromList [1]) topoSpace
fromList [1]

ghci> closure (Set.fromList [1]) topoSpace
fromList [1,2]

\end{showCode}

% TODO: write tests for Kuratowski axioms
