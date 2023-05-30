\section{Semantics}\label{sec:Semantics}


In this module we define the semantics for the formulas defined in \texttt{Syntax.lhs} on both TopoModels and \textbf{S4} Kripke models.

\begin{code}

module Semantics where

import qualified Data.Set as S

import KripkeModels (PointedS4KripkeModel (PS4KM), S4KripkeFrame (S4KF), S4KripkeModel (S4KM))
import Syntax (Form (..))
import TopoModels (PointedTopoModel (..), TopoModel (..))
import Topology (TopoSpace (TopoSpace), openNbds)

\end{code}


\begin{code}

class PointSemantics pointedModel where
    (|=) :: pointedModel -> Form -> Bool

class ModelSemantics model where
    (||=) :: model -> Form -> Bool

\end{code}

% TODO - Write about TopoModel semantics

\begin{code}

instance (Eq a) => PointSemantics (PointedTopoModel a) where
    (|=) :: Eq a => PointedTopoModel a -> Form -> Bool
    (|=) _ Top = True
    (|=) _ Bot = False
    (|=) pointedModel (P n) = x `elem` worldsWherePnTrue
      where
        PointedTopoModel topoModel x = pointedModel
        TopoModel _ valuation = topoModel
        worldsWherePnTrue = snd . S.elemAt 0 $ S.filter (\(p, _) -> p == P n) valuation
    (|=) pointedModel (phi `Dis` psi) = (pointedModel |= phi) || (pointedModel |= psi)
    (|=) pointedModel (phi `Con` psi) = (pointedModel |= phi) && (pointedModel |= psi)
    (|=) pointedModel (phi `Imp` psi) = pointedModel |= (Neg phi `Dis` psi)
    (|=) pointedModel (Neg phi) = not $ pointedModel |= phi
    (|=) pointedModel (Dia phi) = pointedModel |= Neg (Box (Neg phi)) -- TODO - Implement this as a primitive
    (|=) pointedModel (Box phi) = not (null openNbdsSatisfyingFormula)
      where
        PointedTopoModel topoModel point = pointedModel
        TopoModel topoSpace _ = topoModel
        wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x |= psi) set
        openNbdsOfPoint = openNbds point topoSpace
        openNbdsSatisfyingFormula = S.filter (`wholeSetSatisfiesForm` phi) openNbdsOfPoint

instance (Eq a) => ModelSemantics (TopoModel a) where
    topoModel ||= phi = wholeSetSatisfiesForm space phi
      where
        (TopoModel topoSpace _) = topoModel
        TopoSpace space _ = topoSpace
        wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x |= psi) set

\end{code}

% TODO - Write about S4KripkeModel semantics

\begin{code}

instance (Eq a, Ord a) => PointSemantics (PointedS4KripkeModel a) where
    (|=) _ Top = True
    (|=) _ Bot = False
    (|=) pointedModel (P n) = x `elem` worldsWherePnTrue
      where
        PS4KM kripkeModel x = pointedModel
        S4KM _ valuation = kripkeModel
        worldsWherePnTrue = snd . S.elemAt 0 $ S.filter (\(p, _) -> p == P n) valuation
    (|=) pointedModel (phi `Dis` psi) = (pointedModel |= phi) || (pointedModel |= psi)
    (|=) pointedModel (phi `Con` psi) = (pointedModel |= phi) && (pointedModel |= psi)
    (|=) pointedModel (phi `Imp` psi) = pointedModel |= (Neg phi `Dis` psi)
    (|=) pointedModel (Neg phi) = not $ pointedModel |= phi
    (|=) pointedModel (Dia phi) = pointedModel |= Neg (Box (Neg phi)) -- TODO - Implement this as a primitive
    (|=) pointedModel (Box phi) = all (\w' -> PS4KM kripkeModel w' |= phi) imageOfWorld
      where
        (PS4KM kripkeModel world) = pointedModel
        S4KM kripkeFrame _ = kripkeModel
        S4KF _ relation = kripkeFrame
        imageOfWorld = S.map snd $ S.filter (\(x, _) -> x == world) relation

instance (Eq a, Ord a) => ModelSemantics (S4KripkeModel a) where
    kripkeModel ||= phi = wholeSetSatisfiesForm carrier phi
      where
        (S4KM frame _) = kripkeModel
        (S4KF carrier _) = frame
        wholeSetSatisfiesForm set psi = all (\x -> PS4KM kripkeModel x |= psi) set

\end{code}
