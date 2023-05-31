\section{ModelConversion}\label{sec:ModelConversion}

\begin{code}

module Models where

import Data.Set (Set)
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary, Gen)

import SetTheory (subsetOf)
import Syntax (Form (P))
import KripkeModels (S4KripkeFrame)
import TopoModels (TopoModel)

\end{code}

\begin{code}

toTopoModel :: S4KripkeFrame a -> TopoModel a
toTopoModel = undefined

toS4KripkeModel :: TopoModel a -> S4KripkeFrame a
toS4KripkeModel = undefined

\end{code}
