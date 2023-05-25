
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

import Data.Set (Set, cartesianProduct, union, intersection, (\\), elemAt, isSubsetOf)
import qualified Data.Set as Set

unionize :: Ord a => Set (Set a) -> Set (Set a)
unionize sets = Set.map (uncurry union) (cartesianProduct sets sets)

intersectionize :: Ord a => Set (Set a) -> Set (Set a)
intersectionize sets = Set.map (uncurry intersection) (cartesianProduct sets sets)

-- The closure definitions defined below are finite, but it is sufficient for our purposes
-- since we will only work with finite models.
closeUnderUnion :: Ord a => Set (Set a) -> Set (Set a)
closeUnderUnion sets = do
    let oneUp = unionize sets
    if sets == oneUp then sets
    else closeUnderUnion oneUp

closeUnderIntersection :: Ord a => Set (Set a) -> Set (Set a)
closeUnderIntersection sets = do
    let oneUp = intersectionize sets
    if sets == oneUp then sets
    else closeUnderUnion oneUp

\end{code}

Some examples of applying the closure functions:

\begin{showCode}
ghci> closeUnderUnion [[1], [2], [3, 4]]
ghci> [[1],[2],[3,4],[1,2],[1,3,4],[2,3,4],[1,2,3,4]]

ghci> closeUnderIntersection [[1,2,3], [2,3], [3,4]]
ghci> [[1,2,3],[2,3],[3,4],[3]]

ghci> let t = closeUnderIntersection . closeUnderUnion \$ [[1, 2], [1,3], [3, 4]]
ghci> t
ghci> [[1,2],[1,3],[3,4],[1,2,3],[1,2,3,4],[1,3,4],[],[1],[3]]
\end{showCode}

Now, we can define a Topological space in Haskell.

\begin{code}
data  TopoSpace a = TopoSpace (Set a) (Set (Set a))
    deriving (Eq, Show)
\end{code}

The elements of $\tau$ are called \textit{open sets} or \textit{opens}.
A set $C \subseteq X$ is called a \textit{closed set} if it is the complement
of an open set, i.e., it is of the form $X \setminus U$ for some $U \in \tau$.

We let $\overline{\tau} = \{X \setminus U | U \in \tau \}$ denote the family of all
closed sets of $(X, \tau)$.

A set $A \subseteq X$ is called \textit{clopen} if it is both closed and open.

\begin{code}

closeds :: Ord a => TopoSpace a -> Set (Set a)
closeds (TopoSpace space topology) = Set.map (space \\ ) topology

isOpenIn :: Eq a => Set a -> TopoSpace a -> Bool
isOpenIn set (TopoSpace _ opens) = set `elem` opens

isClosedIn :: (Eq a , Ord a) => Set a -> TopoSpace a -> Bool
isClosedIn x ts = x `elem` closeds ts

isClopenIn :: (Eq a , Ord a) => Set a -> TopoSpace a -> Bool
isClopenIn x ts =  x `isOpenIn` ts && x `isClosedIn` ts

\end{code}

Examples of using the above:

\begin{showCode}
ghci> let ts = TopoSpace {space = [1,2,3,4], top = t}
ghci> opens ts
ghci> [[1,2],[1,3],[3,4],[1,2,3],[1,2,3,4],[1,3,4],[],[1],[3]]
ghci> closeds ts
ghci> [[3,4],[2,4],[1,2],[4],[],[2],[1,2,3,4],[2,3,4],[1,2,4]]
ghci> isOpen [1] ts
ghci> True
ghci> isClosed [1] ts
ghci> False
ghci> isClopen [] ts
ghci> True
\end{showCode}

% TODO: write tests for the topology axioms

% TODO: subbasis and basis?

The \textit{interior} of a subset $S$ of a topological space $X$
is the union of all open subsets of $S$.

The \textit{closure} of a subset $S$ of a topological space $X$
is the intersection of all closed subsets containing $S$. 

\begin{code}

arbUnion :: Ord a => Set (Set a) -> Set a
arbUnion = Set.foldr union Set.empty 

arbIntersection :: (Eq a, Ord a) => Set (Set a) -> Set a
arbIntersection sets | sets == Set.empty = error "Cannot take the intersection of the empty set."
                     | length sets == 1  = firstSet
                     | otherwise         = firstSet `intersection` arbIntersection restOfSets
                where
                    firstSet = elemAt 0 sets
                    restOfSets = Set.drop 1 sets

interior :: Ord a => Set a -> TopoSpace a -> Set a
interior set topoSpace = arbUnion opensBelowSet
    where
        TopoSpace _ opens = topoSpace
        opensBelowSet = Set.filter (`isSubsetOf` set) opens

closure :: Ord a => Set a -> TopoSpace a -> Set a
closure set topoSpace = arbIntersection closedsAboveSet
    where
        closedsAboveSet = Set.filter (\c -> set `isSubsetOf` c) (closeds topoSpace)

\end{code}

Examples of using the above:

\begin{showCode}
ghci> powerset [1,2,3]
ghci> [[1,2,3],[1,2],[1,3],[1],[2,3],[2],[3],[]]

ghci> isSubsetEq [] [1,2,3]
ghci> True

ghci> isSubsetEq [1,2] [1,2,3]
ghci> True

ghci> isSubsetEq [1,4] [1,2,3]
ghci> False

ghci> interior [1,2] ts
ghci> [1,2]

ghci> closure [1,2] ts
ghci> [1,2]
\end{showCode}

% TODO: write tests for Kuratowski axioms
