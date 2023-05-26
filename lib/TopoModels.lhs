\section{TopoModels}\label{sec:TopoModels}

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module TopoModels where

import Data.Set (Set)
import qualified Data.Set as S

import Syntax (Form, Form(P))
import Topology (TopoSpace(TopoSpace), setElements, subsetOf)
import Test.QuickCheck ( Arbitrary(arbitrary), Gen)

type Valuation a = Set (Form, Set a)

data TopoModel a = TopoModel (TopoSpace a) (Valuation a)
    deriving (Eq, Show)

data PointedTopoModel a = PointedTopoModel (TopoModel a) a
\end{code}

\begin{code}
-- Recursively make a valuation function. Go through each propositional variable 
-- and assign a subset of points at which it is true
randomVal :: (Arbitrary a, Ord a, Ord Form) => Set a -> [Int] -> Gen (Set (Form, Set a))
randomVal _ [] = return S.empty
randomVal points (prop:props) 
  | null points = return S.empty
  | otherwise = do 
      x <- randomVal points props
      randSubset <- subsetOf points
      return $ S.singleton (P prop, randSubset) `S.union` x

instance (Arbitrary a, Ord a, Ord Form) => Arbitrary (TopoModel a) where
  arbitrary = do
    (TopoSpace space topo) <- arbitrary
    -- Random Valuation depending on the points of the space
    -- Fix the number of propositional variables
    val <- randomVal space [1..10]
    return (TopoModel (TopoSpace space topo) val)

instance (Arbitrary a, Ord a, Ord Form) => Arbitrary (PointedTopoModel a) where
  arbitrary = do 
   (TopoModel (TopoSpace space topo) val) <- arbitrary
   (x :: a) <- setElements space
   return (PointedTopoModel (TopoModel (TopoSpace space topo) val) x)
\end{code}