
\section{Topological Preliminaries}\label{sec:Preliminaries}

This section describes a module which we will import later on.

\begin{code}
module TopoPreliminaries where

-- Enables the ability to not use 'fromList' so much to work
-- smoother with Sets
{-# LANGUAGE OverloadedLists #-}

import Data.List
--import Data.Maybe

--import Data.Set (Set)
--import qualified Data.Set as S

-- [[], [1], [2], [3, 4]] ->
-- [[], [1], [2], [3,4], [1,2], [1,3,4], 
--  [2,3,4], [1,2,3,4]]

eq :: Ord a => [a] -> [a] -> Bool
eq a b = sort a == sort b

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

We can interrupt the code anywhere we want.

\begin{code}
funnyfunction :: Integer -> Integer
funnyfunction 0 = 42
\end{code}

Even in between cases, like here.
It's always good to cite something \cite{Knuth11CombAlg}.

\begin{code}
funnyfunction n | even n    = funnyfunction (n-1)
                | otherwise = n*100
\end{code}

Something to reverse lists.

\begin{code}
myreverse :: [a] -> [a]
myreverse [] = []
myreverse (x:xs) = myreverse xs ++ [x]
\end{code}

That's it, for now.
