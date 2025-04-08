{-# LANGUAGE InstanceSigs, FlexibleInstances, FlexibleContexts #-}

module Explicit.Semantics where

import qualified Data.Set as S
import qualified Data.IntMap as IntMap
import Data.Map.Strict ((!))

import SetTheory (arbIntersection)
import Syntax
import Explicit.TopoEModels
  ( PtTopoEModel
  , TopoEModel (..)
  , sbOpenNbdsOfState
  , cellOfStateTM
  )
import Explicit.KripkeModels
  ( PtS4KripkeModel
  , S4KripkeModel (..)
  , cellOfStateKM, groupRel
  )


{-
  Semantics on the relational and topological representation of topo-e-models.
  Defined on formulas of type Form (defined in Syntax).
-}


class Semantics m where
  (|=) :: m -> Form -> Bool

{-
  Semantics for Form on relational models. The semantics assumes a model such
  that for each agent, points from different information cells are not reachable.
-}
instance Semantics PtS4KripkeModel where
  (|=) _ Top         = True
  (|=) _ Bot         = False
  (|=) (km, x) (PrpF p) = kval km IntMap.! x ! p
  (|=) pm (Neg f)    = not $ pm |= f
  (|=) pm (Conj fs)  = all (pm |=) fs
  (|=) pm (Disj fs)  = any (pm |=) fs
  (|=) pm (Impl f g) = not (pm |= f) || pm |= g
  {-
    Box ags f is true at x, if f is true at every point that is reachable from x
    by all agents in ags. Assuming a correct input, points from different information
    cells are not reachable. Thus, we do not
    account for partitions.
  -}
  (|=) pm (Box ags f)  = all (\y -> (km, y) |= f) imageAgsOfx
    where
      (km, x) = pm
      imageAgsOfx = groupRel ags km ! x
  {-
    Forall ags f is true at x, if f is true at all points in the unique info cell
    for the group ags that contains x.
  -}
  (|=) pm (Forall ags f) = all (\y -> (km, y) |= f) cellAgsOfx
    where
      (km, x) = pm
      cellAgsOfx = cellOfStateKM x ags km
  (|=) pm (Dia ags f)    = pm |= (Neg . Box ags . Neg) f
  (|=) pm (B ags f)      = (pm |=) $ Forall ags $ Dia ags $ Box ags f
  (|=) pm (K ags f)      = pm |= Box ags f && pm |= B ags f

-- Validity of Form on relational models.
instance Semantics S4KripkeModel where
  (|=) :: S4KripkeModel -> Form -> Bool
  km |= f = all (\x -> (km, x) |= f) (kspace km)

{-
  Semantics for Form on topo-e-models. The semantics assumes that the hard evidence
  is disjoint from the soft evidence for each agent.
-}
instance Semantics PtTopoEModel where
  (|=) _ Top         = True
  (|=) _ Bot         = False
  (|=) (tm, x) (PrpF p) = val tm IntMap.! x ! p
  (|=) pm (Neg f)     = not $ pm |= f
  (|=) pm (Conj fs)   = all (pm |=) fs
  (|=) pm (Disj fs)   = any (pm |=) fs
  (|=) pm (Impl f g)  = not (pm |= f) || pm |= g
  {-
    Box ags f is true at x, if the intersection of the factive subbasic evidence
    of the group ags at x supports f. This evidenve includes the unique info cell
    of the group at x, so the set of evidence is nonempty. All evidence contains x,
    so the intersection is nonempty.
  -}
  (|=) pm (Box ags f)   = all (\y -> (tm, y) |= f) (arbIntersection sbbnbds)
    where
      (tm, x) = pm
       -- Manually add the current information cell to the evidence.
      cellAgsOfx = cellOfStateTM x ags tm
      sbbnbds = S.insert cellAgsOfx $ sbOpenNbdsOfState x ags tm
  {-
    Forall ags f is true at x, if the unique info cell of the group that contains
    x supports f.
  -}
  (|=) pm (Forall ags f) = all satf cellAgsOfx
    where
      (tm, x) = pm
      satf y = (tm, y) |= f
      cellAgsOfx = cellOfStateTM x ags tm
  (|=) pm (Dia ags f)    = pm |= (Neg . Box ags . Neg) f
  (|=) pm (B ags f)      = (pm |=) $ Forall ags $ Dia ags $ Box ags f
  (|=) pm (K ags f)      = pm |= Box ags f && pm |= B ags f

-- Validity of Form on topo-e-models.
instance Semantics TopoEModel where
  tm |= f = all (\y -> (tm, y) |= f) (space tm)