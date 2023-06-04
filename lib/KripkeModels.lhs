\section{Kripke models}\label{sec:KripkeModels}

In this section we define relational models of modal logic. \\

\begin{code}

{-# LANGUAGE ScopedTypeVariables #-}

module KripkeModels where

import Data.Set (Set, cartesianProduct, union)
import qualified Data.Set as S
import Test.QuickCheck (Arbitrary (arbitrary), suchThat, chooseInt)

import Models (Valuation, randomVal)
import SetTheory (Relation, isOfSizeBetween, makeTransitive, setElements, subsetSizeOf)

\end{code}

\subsection{Kripke models}

An \emph{$\SFour$ Kripke frame} is a tuple $(X, R)$ where $X$ is a set and $R \sub X \times X$ and the following are true for all $x, y, z \in X$.
\begin{itemize}
    \item$xRx$ \hspace{4cm}(Reflexivity) 
    \item$xRy$ and $yRz$ implies $xRz$ \hspace{0.05cm}(Transitivity) 
\end{itemize}

An \emph{$\SFour$ Kripke model} is a triple $(X, R, V)$ where $(X, R)$ is an $\SFour$ Kripke frame and $V$ is a valuation on $X$.

A \emph{pointed $\SFour$ Kripke model} is a 4-tuple $(X, R, V, x)$ where $(X, R, V)$ is an $\SFour$ Kripke model and $x \in X$. \\

\begin{code}

data S4KripkeFrame a = S4KF (Set a) (Relation a)
    deriving (Eq, Show)

data S4KripkeModel a = S4KM (S4KripkeFrame a) (Valuation a)
    deriving (Eq, Show)

data PointedS4KripkeModel a = PS4KM (S4KripkeModel a) a
    deriving (Eq, Show)

\end{code}

\subsection{Arbitrary Kripke model generation}

Below we define a method for generating arbitrary Kripke models.
This presented something of an interesting challenge as we cannot simply take \emph{any} relation on \emph{any} carrier set; we must ensure that the generated frame is, indeed, $\SFour$ (i.e. reflexive and transitive).

To accomplish this, we generate an arbitrary carrier set and an arbitrary subset of its cartesian product.
We then add to this random relation all of the reflexive pairs and close it under transitive triples.

This closure process grows the relation significantly so, in order to avoid ending up with a complete graph, we choose a starting relation that is quite small.
Given a carrier set of cardinality $n$, instead of allowing any subset of the cross product (which could be as large as $n^2$), we capped the random relation at cardinality $2n$, which ensures that we get interesting frames. \\

\begin{code}

instance (Arbitrary a, Ord a) => Arbitrary (S4KripkeFrame a) where
    arbitrary = do
        (carrier :: Set a) <- arbitrary `suchThat` (\set -> isOfSizeBetween set 1 10)
        let carrierSquared = cartesianProduct carrier carrier
        {-
            If no cap is put on this then the resulting frame (after being made
            reflexive and transitive) will almost always be a complete graph,
            which is uninteresting.
        -}
        k <- chooseInt (1, S.size carrier * 3)
        (randomRelation :: Relation a) <- subsetSizeOf carrierSquared k 
        let diagonal = S.filter (uncurry (==)) carrierSquared
        let reflexiveRelation = randomRelation `union` diagonal
        let s4Relation = makeTransitive reflexiveRelation
        return (S4KF carrier s4Relation)

instance (Arbitrary a, Ord a) => Arbitrary (S4KripkeModel a) where
    arbitrary = do
        (randomFrame :: S4KripkeFrame a) <- arbitrary
        let (S4KF carrier _) = randomFrame
        (randomValuation :: Valuation a) <- randomVal carrier [1 .. 10]
        return (S4KM randomFrame randomValuation)

instance (Arbitrary a, Ord a) => Arbitrary (PointedS4KripkeModel a) where
    arbitrary = do
        (randomModel :: S4KripkeModel a) <- arbitrary
        let (S4KM frame _) = randomModel
        let (S4KF carrier _) = frame
        point <- setElements carrier
        return (PS4KM randomModel point)

\end{code}