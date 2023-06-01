\section{Models}\label{sec:Models}

\begin{code}

module Models where

import Data.Set (Set)
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary, Gen)

import SetTheory (subsetOf)
import Syntax (Form (P))

\end{code}

\begin{code}

type Valuation a = Set (Form, Set a)

-- Recursively make a valuation function. Go through each propositional variable
-- and assign a subset of points at which it is true
randomVal :: (Arbitrary a, Ord a) => Set a -> [Int] -> Gen (Valuation a)
randomVal _ [] = return S.empty
randomVal points (prop : props)
    | null points = return S.empty
    | otherwise = do
        x <- randomVal points props
        randSubset <- subsetOf points
        return $ S.singleton (P prop, randSubset) `S.union` x

\end{code}
