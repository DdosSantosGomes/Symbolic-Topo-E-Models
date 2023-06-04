\section{Topological preliminaries}\label{sec:Topology}

In this section we define basic topological concepts that will form the foundation for our subsequent definition of topomodels and toposemantics for modal logic.
For a more exhaustive treatment of topological structures, see \cite{Eng89}.\\

\begin{code}

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Topology where

import Data.Set (Set, isSubsetOf, singleton, union, (\\))
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary (arbitrary), suchThat)

import SetTheory (arbIntersection, arbUnion, closeUnderIntersection, closeUnderUnion, isOfSizeBetween, setElements, setOf1)

\end{code}

\subsection{Topological spaces}

A \emph{topological space} (or \emph{topospace}) is a tuple $(X, \tau)$ where $X$ is a non-empty set and $\tau \sub \pset{X}$ is a family of subsets of $X$ such that
\begin{enumerate}
  \item $\empty, X \in \tau$
  \item $S \sub \tau$ and $|S| < \omega$ implies $\biginter S \in \tau$
  \item $S \sub \tau$ implies $\bigunion S \in \tau$
\end{enumerate}

\begin{code}

type Topology a = Set (Set a)

data TopoSpace a = TopoSpace (Set a) (Topology a) deriving (Eq, Show)

\end{code}

The elements of $\tau$ are referred to as \emph{open sets}, so we say a subset $S \sub X$ is \emph{open} in $\tau$ if $S \in \tau$.
Given a point $x \in X$, we call the set of all open sets containing $x$ the \emph{open neighbourhoods of $x$}.

Additionally, we say that $S$ is \emph{closed} (in $\tau$) if $X - A \in \tau$ (i.e. $S$ is the complement of an open set).
The set of closed sets of $(X, \tau)$ is denoted by $\closure{\tau}$.

Finally, we say that $S$ is \emph{clopen} if it is both open and closed. \\

\begin{code}

isOpenIn :: (Eq a) => Set a -> TopoSpace a -> Bool
isOpenIn set (TopoSpace _ topology) = set `elem` topology

openNbds :: (Eq a) => a -> TopoSpace a -> Set (Set a)
openNbds x (TopoSpace _ topology) = S.filter (x `elem`) topology

isClosedIn :: (Eq a, Ord a) => Set a -> TopoSpace a -> Bool
isClosedIn set (TopoSpace space topology) = space \\ set `elem` topology

closeds :: (Ord a) => TopoSpace a -> Set (Set a)
closeds (TopoSpace space topology) = S.map (space \\) topology

isClopenIn :: (Eq a, Ord a) => Set a -> TopoSpace a -> Bool
isClopenIn set topoSpace = set `isOpenIn` topoSpace && set `isClosedIn` topoSpace

\end{code}

Given a topospace $(X, \tau)$ and a subset $S \sub X$, the \emph{interior} of $S$, denoted by $\interior{S}$, is the union of all open subsets of $S$, i.e.
  \[ \interior{S} := \bigunion \compin{U}{\tau}{U \sub S}\]

The \emph{closure} of $S$, denoted by $\closure{S}$, is the intersection of all closed supersets of $S$, i.e.
  \[ \closure{S} := \biginter \compin{C}{\closure{\tau}}{S \sub C}\]

\begin{code}

interior :: (Ord a) => Set a -> TopoSpace a -> Set a
interior set topoSpace = arbUnion opensBelowSet
  where
    TopoSpace _ opens = topoSpace
    opensBelowSet = S.filter (`isSubsetOf` set) opens

closure :: (Ord a) => Set a -> TopoSpace a -> Set a
closure set topoSpace = arbIntersection closedsAboveSet
  where
    closedsAboveSet = S.filter (set `isSubsetOf`) (closeds topoSpace)

\end{code}

\subsection{Bases and Subbases}

Given a topological space $\XX := (X, \tau)$, a \emph{basis} for $\XX$ is a subset $\beta \sub \tau$ such that $\tau$ is equal to the closure of $\beta$ under arbitrary unions.

A \emph{subbasis} for $\XX$ is a subset $\sigma \sub \tau$ such that the closure of $\sigma$ under finite intersections forms a basis for $\XX$. \\

\begin{code}

isBasisFor :: (Ord a) => Set (Set a) -> TopoSpace a -> Bool
isBasisFor sets (TopoSpace _ opens) = closeUnderUnion sets == opens

isSubbasisFor :: (Ord a) => Set (Set a) -> TopoSpace a -> Bool
isSubbasisFor sets topoSpace = closeUnderIntersection sets `isBasisFor` topoSpace

\end{code}

\subsection{Arbitrary topological spaces}

First we include a couple of helper functions.

The first of them checks if the passed \verb|TopoSpace| is, indeed, a topological space (i.e. respects all of the axioms).

The second actually \emph{fixes} a passed \verb|TopoSpace| in the case that it is not \emph{truly} a topological space (i.e. fails to satisfy one of the axioms).
This is necessary for the generation of arbitrary topospaces later on. \\

\begin{code}

isTopoSpace :: (Ord a) => TopoSpace a -> Bool
isTopoSpace (TopoSpace space topology)
    -- Passed space is empty
    | space == S.empty = False
    -- Passed topology is not a subset of the power set of passed space
    | not (arbUnion topology `isSubsetOf` space) = False
    -- Passed topology is missing the empty set or the full space
    | S.empty `notElem` topology || space `notElem` topology = False
    -- Passed topology should be closed under intersections and unions
    | otherwise = topology == (closeUnderUnion . closeUnderIntersection) topology

fixTopoSpace :: (Ord a) => TopoSpace a -> TopoSpace a
fixTopoSpace (TopoSpace space topology)
    -- Throw an error since we don't know how the topology should look like
    | not (S.unions topology `isSubsetOf` space) = error "Points in topology are not all members of the space"
    | S.empty `notElem` topology = fixTopoSpace (TopoSpace space (topology `union` singleton S.empty))
    | space `notElem` topology = fixTopoSpace (TopoSpace space (topology `union` singleton space))
    | otherwise = TopoSpace space closedTopology
  where
    closedTopology = closeUnderUnion . closeUnderIntersection $ topology

\end{code}

Now we can define a method for generating arbitrary topospaces. \\

\begin{code}

instance (Arbitrary a, Ord a) => Arbitrary (TopoSpace a) where
    arbitrary = do
        (x :: Set a) <- arbitrary `suchThat` (\set -> isOfSizeBetween set 1 10)
        -- Put an artificial bound on the size of the set, otherwise it takes too long to "fix" the topology
        subbasis <-
            let basis = setOf1 (setElements x) `suchThat` (\set -> isOfSizeBetween set 0 3)
             in setOf1 basis `suchThat` (\set -> isOfSizeBetween set 0 3)
        let someTopoSpace = TopoSpace x subbasis
        return (fixTopoSpace someTopoSpace)

\end{code}

% ----------------------------------------------------------------------------------------------------------------------
% We have to decide if we want to include these. -----------------------------------------------------------------------
% ----------------------------------------------------------------------------------------------------------------------

% Here we initialise a few sets to test our implementations of topological concepts going forward. \\

% \begin{showCode}
% ghci> (s0 :: Set Int) = S.fromList [1]
% ghci> (s1 :: Set Int) = S.fromList [2]
% ghci> (s2 :: Set Int) = S.fromList [3, 4]
% ghci> (s3 :: Set Int) = S.fromList [1, 2, 3]
% ghci> (s4 :: Set Int) = S.fromList [2, 3]
% ghci> (s5 :: Set Int) = S.fromList [3, 4]
% ghci> (s6 :: Set Int) = S.fromList [1, 2]
% ghci> (s7 :: Set Int) = S.fromList [1, 3]
% \end{showCode}

% Here we provide some examples of closure under intersections and unions.

% \begin{showCode}

% ghci> closeUnderUnion $ S.fromList [s0, s1, s2]
% fromList [fromList [1],fromList [1,2],fromList [1,2,3,4],fromList [1,3,4],fromList [2],fromList [2,3,4],fromList [3,4]]

% ghci> closeUnderIntersection $ S.fromList [s0, s1, s2]
% fromList [fromList [],fromList [1],fromList [2],fromList [3,4]]

% ghci> closeUnderUnion $ S.fromList [s3, s4, s5]
% fromList [fromList [1,2,3],fromList [1,2,3,4],fromList [2,3],fromList [2,3,4],fromList [3,4]]

% ghci> closeUnderIntersection $ S.fromList [s3, s4, s5]
% fromList [fromList [1,2,3],fromList [2,3],fromList [3],fromList [3,4]]

% ghci> topology = (closeUnderUnion . closeUnderIntersection) $ S.fromList [s5, s6, s7]
% ghci> topology
% fromList [fromList [],fromList [1],fromList [1,2],fromList [1,2,3],fromList [1,2,3,4],fromList [1,3],fromList [1,3,4],fromList [3],fromList [3,4]]

% $\end{showCode}


% Examples of using the above:
% \begin{showCode}
% ghci> isTopoSpace (TopoSpace (arbUnion $ S.fromList [s5, s6, s7]) topology)
% ghci> True

% ghci> badTS = TopoSpace (S.fromList [1,2,3]) (S.fromList [S.fromList [1,2], S.fromList[2,3]])
% ghci> isTopoSpace badTS
% ghci> False

% ghci> goodTS = fixTopoSpace badTS
% ghci> isTopoSpace goodTS
% ghci> True

% ghci> isTopoSpace (fixTopoSpace goodTS)
% ghci> True

% ghci> fixTopoSpace (TopoSpace (S.fromList [1,2,3]) topology)
% ghci> error "topology not a subset of the power set of the space"
% $\end{showCode}

% Examples of using the above:

% \begin{showCode}

% ghci> topoSpace = TopoSpace (S.fromList [1, 2, 3, 4]) topology

% ghci> closeds topoSpace
% fromList [fromList [],fromList [1,2],fromList [1,2,3,4],fromList [1,2,4],fromList [2],fromList [2,3,4],fromList [2,4],fromList [3,4],fromList [4]]

% ghci> openNbds 2 topoSpace
% fromList [fromList [1,2],fromList [1,2,3],fromList [1,2,3,4]]

% ghci> S.fromList [1] `isOpenIn` topoSpace
% True
% ghci> S.fromList [1] `isClosedIn` topoSpace
% False
% ghci> S.fromList [] `isClopenIn` topoSpace
% True

% \end{showCode}


% Examples of using the above:

% \begin{showCode}

% ghci> interior (S.fromList [1]) topoSpace
% fromList [1]

% ghci> closure (S.fromList [1]) topoSpace
% fromList [1,2]

% \end{showCode}
