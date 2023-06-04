\section{Topomodels}\label{sec:TopoModels}

In this section we define topological models of modal logic. \\

\begin{code}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TopoModels where

import Test.QuickCheck (Arbitrary (arbitrary))

import Models (Valuation, randomVal)
import SetTheory (setElements)
import Topology (TopoSpace (TopoSpace))

\end{code}

\subsection{Topomodels}

A \emph{topomodel} is a triple $(X, \tau, V)$ where $(X, \tau)$ is a topospace and $V$ is a valuation on $X$.

A \emph{pointed topomodel} is a 4-tuple $(X, \tau, V, x)$ where $(X, \tau, V)$ is an topomodel and $x \in X$. \\

\begin{code}

data TopoModel a = TopoModel (TopoSpace a) (Valuation a)
    deriving (Eq, Show)

data PointedTopoModel a = PointedTopoModel (TopoModel a) a
    deriving (Eq, Show)

\end{code}

\subsection{Arbitrary topomodel generation}

Below we define a method for generating arbitrary topomodels.

% TODO - Talk about some of the interesting challenges or implementation details

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