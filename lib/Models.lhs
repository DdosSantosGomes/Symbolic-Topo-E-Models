\section{Models}\label{sec:Models}

In this section we define some concepts that will be used in the subsequent sections on \emph{Kripke models} and \emph{topomodels}. \\

\begin{code}

module Models where

import Data.Set (Set, union)
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary, Gen)

import SetTheory (subsetOf)
import Syntax (Form (P))

\end{code}

\subsection{Arbitrary valuation generation}

Given a set $X$, a \emph{valuation} is a function $V: \Prop \to \pset{X}$ where $\Prop$ is the set of formulas of the shape $p_n$.

\emph{Note:} The type of \verb|Valuation| below suggests our valuations should be defined on all \verb|Form| (instead of just on $\Prop$), but this is merely an implementation detail and when generating arbitrary \verb|Valuation|'s we only define them on $\Prop$. \\

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
        return $ S.singleton (P prop, randSubset) `union` x

\end{code}
