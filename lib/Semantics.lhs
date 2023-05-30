\section{Semantics}\label{sec:Semantics}


\begin{code}

module Semantics where

import qualified Data.Set as S

import Syntax
import TopoModels
import Topology

satisfies :: (Eq a) => PointedTopoModel a -> Form -> Bool
satisfies _ Top = True
satisfies _ Bot = False
satisfies pointedModel (P n) = x `elem` worldsWherePnTrue
  where
    PointedTopoModel topoModel x = pointedModel
    TopoModel _ valuation = topoModel
    worldsWherePnTrue = snd . S.elemAt 0 $ S.filter (\(p, _) -> p == P n) valuation
satisfies pointedModel (phi `Dis` psi) = pointedModel `satisfies` Neg (Neg phi `Con` Neg psi)
satisfies pointedModel (phi `Con` psi) = (pointedModel `satisfies` phi) && (pointedModel `satisfies` psi)
satisfies pointedModel (phi `Imp` psi) = pointedModel `satisfies` (Neg phi `Dis` psi)
satisfies pointedModel (Neg phi) = not $ pointedModel `satisfies` phi
satisfies pointedModel (Dia phi) = pointedModel `satisfies` Neg (Box (Neg phi))
satisfies pointedModel (Box phi) = not (null openNbdsSatisfyingFormula)
  where
    PointedTopoModel topoModel point = pointedModel
    TopoModel topoSpace _ = topoModel
    wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x `satisfies` psi) set
    openNbdsOfPoint = openNbds point topoSpace
    openNbdsSatisfyingFormula = S.filter (`wholeSetSatisfiesForm` phi) openNbdsOfPoint

(|=) :: (Eq a) => PointedTopoModel a -> Form -> Bool
pointedModel |= phi = pointedModel `satisfies` phi

(||=) :: (Eq a) => TopoModel a -> Form -> Bool
topoModel ||= phi = wholeSetSatisfiesForm space phi
  where
    (TopoModel topoSpace _) = topoModel
    TopoSpace space _ = topoSpace
    wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x `satisfies` psi) set

\end{code}
