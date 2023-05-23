
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

unionize :: (Eq a, Ord a) => [[a]] -> [[a]]
unionize [] = []
unionize xs = sort . nub $ [sort (x `union` y) | x <- xs, y <- xs, x /= y]

intersectionize :: (Eq a, Ord a) => [[a]] -> [[a]]
intersectionize [] = []
intersectionize xs = sort . nub $ [sort (x `intersect` y) | x <- xs, y <- xs, x /= y]

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

Now, we can define a Topological space in Haskell.

\begin{code}
data  TopSpace a = TopSpace { 
  space :: [a]
, top :: [[a]]
}
\end{code}

The elements of $\tau$ are called \textit{open sets} or \textit{opens}.
A set $C \subseteq X$ is called a \textit{closed set} if it is the complement
of an open set, i.e., it is of the form $X \setminus U$ for some $U \in \tau$.

We let $\overline{\tau} = \{X \setminus U | U \in \tau \}$ denote the family of all
closed sets of $(X, \tau)$.

A set $A \subseteq X$ is called \textit{clopen} if it is both closed and open.

\begin{code}
opens :: TopSpace a -> [[a]]
opens = top

closeds :: (Eq a) => TopSpace a -> [[a]]
closeds ts = [space ts \\ open | open <- top ts]

isOpen :: (Eq a) => [a] -> TopSpace a -> Bool
isOpen x ts = x `elem` opens ts

isClosed :: (Eq a) => [a] -> TopSpace a -> Bool
isClosed x ts = x `elem` closeds ts

isClopen :: (Eq a) => [a] -> TopSpace a -> Bool
isClopen x ts = isOpen x ts && isClosed x ts
\end{code}

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

interior :: (Eq a) => [a] -> TopSpace a -> [a]
interior xs ts = concat [ u | u <- top ts, isSubsetEq u xs]

closure :: (Eq a) => [a] -> TopSpace a -> [a]
closure xs ts = concat [ u | u <- closeds ts, isSubsetEq xs u]

\end{code}











