\section{Semantics}\label{sec:Semantics}


\begin{code}

module Semantics where

import Syntax
import Topology
import TopoModels


satisfies :: Eq a => PointedTopoModel a -> Form -> Bool
satisfies _ Top = True
satisfies _ Bot = False
satisfies pointedModel (P n) = x `elem` valuation (P n)
    where
        PointedTopoModel topoModel x = pointedModel
        TopoModel _ valuation = topoModel
satisfies pointedModel (phi `Dis` psi) = pointedModel `satisfies` Neg (Neg phi `Con` Neg psi)
satisfies pointedModel (phi `Con` psi) = (pointedModel `satisfies` phi) && (pointedModel `satisfies` psi)
satisfies pointedModel (phi `Imp` psi) = pointedModel `satisfies` (Neg phi `Dis` psi)
satisfies pointedModel (Neg phi) = not $ pointedModel `satisfies` phi
satisfies pointedModel (Dia phi) = pointedModel `satisfies` Neg (Box (Neg phi))
satisfies pointedModel (Box phi) = not (null openNeighbourhoodsContainedInTruthSet)
    where
        PointedTopoModel topoModel point = pointedModel
        TopoModel topoSpace _ = topoModel
        TopoSpace space topology = topoSpace
        truthSet = [x | x <- space, PointedTopoModel topoModel x `satisfies` phi]
        openNeighbourhoodsContainedInTruthSet = [openSet | openSet<-topology, point `elem` openSet, openSet `isSubsetEq` truthSet]

(|=) :: Eq a => PointedTopoModel a -> Form -> Bool
pointedModel |= phi = pointedModel `satisfies` phi

(||=) :: Eq a => TopoModel a -> Form -> Bool
topoModel ||= phi = all (\x -> PointedTopoModel topoModel x |= phi) space
    where
        (TopoModel topoSpace _) = topoModel
        TopoSpace space _ = topoSpace

\end{code}
