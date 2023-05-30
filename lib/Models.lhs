\section{Models}\label{sec:Models}

\begin{code}

module Models where

import Data.Set (Set)
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary, Gen)

import Syntax (Form(P))
import Topology (subsetOf) {- FIXME - We shouldn't have to import Topology
for access to this. It should probably live in some other module that does
set-theoretic stuff.
-}

\end{code}

\begin{code}

type Valuation a = Set (Form, Set a)

-- Recursively make a valuation function. Go through each propositional variable 
-- and assign a subset of points at which it is true
randomVal :: (Arbitrary a, Ord a) => Set a -> [Int] -> Gen (Set (Form, Set a))
randomVal _ [] = return S.empty
randomVal points (prop:props) 
  | null points = return S.empty
  | otherwise = do 
      x <- randomVal points props
      randSubset <- subsetOf points
      return $ S.singleton (P prop, randSubset) `S.union` x

\end{code}
