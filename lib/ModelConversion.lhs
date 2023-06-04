\section{Model conversion}\label{sec:ModelConversion}

In this sections, we implement a method for converting \verb|S4KripkeModel|'s to \verb|TopoModel|'s and vice-versa.
We follow the construction described in \cite[22-23]{Pac17}. \\

\begin{code}

module ModelConversion where

import Data.Set (cartesianProduct, member, singleton)
import qualified Data.Set as S

import KripkeModels (PointedS4KripkeModel (PS4KM), S4KripkeFrame (S4KF), S4KripkeModel (S4KM))
import SetTheory (closeUnderUnion, imageIn)
import TopoModels (PointedTopoModel (PointedTopoModel), TopoModel (TopoModel))
import Topology (TopoSpace (TopoSpace), closure)

\end{code}

Given an ordered set $\XX := (X, R)$, an \emph{upset} is a subset $S \sub X$ that satisfies the following for all $x, y \in X$.
  \[x \in S \text{ and } xRy \text{ implies } y \in S\]
The term `upset' is used because orders are often depicted using Hasse diagrams where $xRy$ is depicted by the point $y$ being on above $x$, connected by a line.
We denote the set of all upsets of $\XX$ by $\Up(\XX)$.

Given an $\SFour$ Kripke frame $\XX := (X, R)$, it is a well known fact that $(X, \Up(\XX))$ is a topological space.
What is more, for all modal formulas $\varphi$, all valuations $V$ on $X$, and all points $x \in X$, we have
  \[(X, R, V, x) \models \varphi \miff (X, \Up(\XX), V, x) \models \varphi\]
Observe how the `${\models}$' on the left-hand-side is a relational semantics while on the right-hand-side it is a topo-semantics.

Below we implement this conversion from \verb|S4KripkeModel|'s to \verb|TopoModel|'s. \\

\begin{code}

-- Neighborhood Semantics for Modal Logic (Pacuit)

{-
    Here we make use of the following two facts true an all finite pre-orders:
        1. All upsets are (finite) unions of principle upsets or the empty set
        2. All principle upsets are images of points
-}
toTopoSpace :: (Ord a) => S4KripkeFrame a -> TopoSpace a
toTopoSpace kripkeFrame = TopoSpace carrier opens
  where
    S4KF carrier relation = kripkeFrame
    nonEmptyUpsets = closeUnderUnion $ S.map (`imageIn` relation) carrier
    opens = S.insert S.empty nonEmptyUpsets

\end{code}

Now we turn to the other conversion.

Given a topospace $(\XX := (X, \tau))$, the \emph{specialisation order $\RX$ on $\XX$} is defined as follows for all $x, y \in \XX$.
  \[ x \RX y ~:\Longleftrightarrow~ y \in \closure{\set{x}}\]
It follows quite easily that this relation is reflexive and transitive, implying that $(X, \RX)$ is an $\SFour$ Kripke frame.

Similarly to the other conversion, we get the following for all modal formulas $\varphi$, all valuations $V$ on $X$, and all points $x \in X$.
  \[(X, \tau, V, x) \models \varphi \miff (X, \RX, V, x) \models \varphi\]

\begin{code}

toS4KripkeFrame :: (Ord a) => TopoSpace a -> S4KripkeFrame a
toS4KripkeFrame topoSpace = S4KF space relation
  where
    (TopoSpace space _) = topoSpace
    relation = S.filter (\(x, y) -> y `member` closure (singleton x) topoSpace) (cartesianProduct space space)

\end{code}

Since the carrier sets and valuations remain unchanged, we can extend these conversions to (pointed) models. \\

\begin{code}

toTopoModel :: (Ord a) => S4KripkeModel a -> TopoModel a
toTopoModel (S4KM frame valuation) = TopoModel (toTopoSpace frame) valuation

toS4KripkeModel :: (Ord a) => TopoModel a -> S4KripkeModel a
toS4KripkeModel (TopoModel topoSpace valuation) = S4KM (toS4KripkeFrame topoSpace) valuation

toPointedTopoModel :: (Ord a) => PointedS4KripkeModel a -> PointedTopoModel a
toPointedTopoModel (PS4KM kripkeModel point) = PointedTopoModel (toTopoModel kripkeModel) point

toPointedS4KripkeModel :: (Ord a) => PointedTopoModel a -> PointedS4KripkeModel a
toPointedS4KripkeModel (PointedTopoModel topoModel point) = PS4KM (toS4KripkeModel topoModel) point

\end{code}
