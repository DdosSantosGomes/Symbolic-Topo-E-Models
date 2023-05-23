
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













