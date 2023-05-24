
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

import Data.List

-- TODO: workaround nub somehow?
-- Notion of set equality on lists
eq :: Ord a => [a] -> [a] -> Bool
eq x y = sort (nub x) == sort (nub y)

unionize :: (Eq a, Ord a) => [[a]] -> [[a]]
unionize [] = []
unionize xs = sort . nub $ [sort (x `union` y) | x <- xs, y <- xs, x /= y]

intersectionize :: (Eq a, Ord a) => [[a]] -> [[a]]
intersectionize [] = []
intersectionize xs = sort . nub $ [sort (x `intersect` y) | x <- xs, y <- xs, x /= y]

-- The closure definitions defined below are finite, but it is sufficient for our purposes
-- since we will only work with finite models.
closeUnderUnion :: (Eq a, Ord a) => [[a]] -> [[a]]
closeUnderUnion [] = []
closeUnderUnion xs = do
 let oneUp = nub (xs ++ unionize xs)
 if xs == oneUp  then xs
 else closeUnderUnion oneUp

closeUnderIntersection :: (Eq a, Ord a) => [[a]] -> [[a]]
closeUnderIntersection [] = []
closeUnderIntersection xs = do
 let oneUp = nub (xs ++ intersectionize xs)
 if xs == oneUp  then xs
 else closeUnderIntersection oneUp
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
data  TopoSpace a = TopoSpace { 
  space :: [a]
, top :: [[a]]
} deriving (Show)
\end{code}

The elements of $\tau$ are called \textit{open sets} or \textit{opens}.
A set $C \subseteq X$ is called a \textit{closed set} if it is the complement
of an open set, i.e., it is of the form $X \setminus U$ for some $U \in \tau$.

We let $\overline{\tau} = \{X \setminus U | U \in \tau \}$ denote the family of all
closed sets of $(X, \tau)$.

A set $A \subseteq X$ is called \textit{clopen} if it is both closed and open.

\begin{code}
opens :: TopoSpace a -> [[a]]
opens = top

closeds :: (Eq a) => TopoSpace a -> [[a]]
closeds ts = [space ts \\ open | open <- top ts]

isOpen :: (Eq a) => [a] -> TopoSpace a -> Bool
isOpen x ts = x `elem` opens ts

isClosed :: (Eq a) => [a] -> TopoSpace a -> Bool
isClosed x ts = x `elem` closeds ts

isClopen :: (Eq a) => [a] -> TopoSpace a -> Bool
isClopen x ts = isOpen x ts && isClosed x ts
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
powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

-- Equivalent property taken from https://en.wikipedia.org/wiki/Subset#Properties
isSubsetEq :: (Eq a) => [a] -> [a] -> Bool
isSubsetEq xs ys = (xs `intersect` ys) == xs

interior :: (Eq a, Ord a) => [a] -> TopoSpace a -> [a]
interior xs ts = sort . nub . concat $ [ u | u <- top ts, isSubsetEq u xs]

arbIntersect :: (Eq a) => [[a]] -> [a]
arbIntersect xs = foldr intersect (concat xs) xs

closure :: (Eq a, Ord a) => [a] -> TopoSpace a -> [a]
closure xs ts = sort . nub . arbIntersect $ [ u | u <- closeds ts, isSubsetEq xs u]
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
