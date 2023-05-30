\section{TopoModels}\label{sec:TopoModels}

\begin{code}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TopoModels where

import Test.QuickCheck (Arbitrary (arbitrary))

import Models (Valuation, randomVal)
import SetTheory (setElements)
import Topology (TopoSpace (TopoSpace))

data TopoModel a = TopoModel (TopoSpace a) (Valuation a)
    deriving (Eq, Show)

data PointedTopoModel a = PointedTopoModel (TopoModel a) a
    deriving (Eq, Show)

\end{code}

\begin{code}

instance (Arbitrary a, Ord a) => Arbitrary (TopoModel a) where
  arbitrary = do
    (TopoSpace space topo) <- arbitrary
    -- Random Valuation depending on the points of the space
    -- Fix the number of propositional variables
    val <- randomVal space [1..10]
    return (TopoModel (TopoSpace space topo) val)

instance (Arbitrary a, Ord a) => Arbitrary (PointedTopoModel a) where
  arbitrary = do 
   (TopoModel (TopoSpace space topo) val) <- arbitrary
   (x :: a) <- setElements space
   return (PointedTopoModel (TopoModel (TopoSpace space topo) val) x)

\end{code}