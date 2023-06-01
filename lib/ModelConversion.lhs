\section{ModelConversion}\label{sec:ModelConversion}

\begin{code}

module ModelConversion where

import Data.Set (cartesianProduct, member, singleton)
import Data.Set qualified as S

import KripkeModels (PointedS4KripkeModel (PS4KM), S4KripkeFrame (S4KF), S4KripkeModel (S4KM))
import SetTheory (closeUnderUnion, imageIn)
import TopoModels (PointedTopoModel (PointedTopoModel), TopoModel (TopoModel))
import Topology (TopoSpace (TopoSpace), closure)

\end{code}

% TODO - Write about equivalence of models

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

toS4KripkeFrame :: (Ord a) => TopoSpace a -> S4KripkeFrame a
toS4KripkeFrame topoSpace = S4KF space relation
  where
    (TopoSpace space _) = topoSpace
    relation = S.filter (\(x, y) -> y `member` closure (singleton x) topoSpace) (cartesianProduct space space)

\end{code}

We can extend this definition to (pointed) models.

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
