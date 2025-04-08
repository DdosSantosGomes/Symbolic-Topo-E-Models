{-# LANGUAGE ImportQualifiedPost, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module Explicit.KripkeModels where

import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Data.Set qualified as S
import Data.Set (Set)
import SMCDEL.Language
  ( Agent
  , Pointed
  , freshp
  )
import Test.QuickCheck
  ( Arbitrary (arbitrary)
  , suchThat
  , Gen
  , sublistOf
  , choose
  )

import SetTheory
  ( Relation
  , isOfSizeBetween
  , makeTransitive
  , makeReflexive
  , World
  , setElements
  , arbIntersection
  )
import Syntax (defaultVocab, defaultAgents, Group)
import Explicit.TopoEModels
  ( Valuation
  , randomVal
  , Partition
  , randomPartMap
  )


{-
  An explicit representation of relational topo-e-models, including arbitrary model generation.
-}


{-
  This type does not enforce that points in different partition cells are not
  related by rel. We do assume this property in the semantics, and the semantics
  returns incorrect evaluations on models that do not satisfy the property.
-}
data S4KripkeModel = S4KM
  { kspace :: Set World                 -- Full space
  , rel    :: M.Map Agent Relation      -- Map from agents to their preorders
  , kpart  :: M.Map Agent Partition     -- Map from agents to their partitions
  , kval   :: Valuation                 -- Valuation
  } deriving (Eq, Show)

instance Pointed S4KripkeModel World
type PtS4KripkeModel = (S4KripkeModel, World)

{-
  Given a state x, a group ags, and an explicit Kripke model km, compute the unique
  information cell for the group that contains x.
  Note: this function is unsafe. It assumes that "kpart km i" is a valid partition,
  s.t. "cellOf i" is the head of a singleton list.
-}
cellOfStateKM :: World -> Group -> S4KripkeModel -> Set World
cellOfStateKM x ags km = arbIntersection allInfoCells where
  cellOf i =  head [c | c <- S.toList (kpart km ! i), x `elem` c]
  allInfoCells = S.fromList [cellOf i | i <- S.toList ags]

{-
  Given a group ags and an explicit Kripke model km, get the evidence
  pre-order for the group by computing the intersection of individual images
  at each world in the state space.
-}
groupRel :: Group -> S4KripkeModel -> Relation
groupRel ags km = M.fromList [(w,  imageForAgs w) | w <- worlds] where
  worlds = S.toList $ kspace km
  imagePerAg w = [(rel km ! i) ! w | i <- S.toList ags]
  imageForAgs w = arbIntersection $ S.fromList (imagePerAg w)


-- Arbitrary Kripke Model generation


{-
  Given a space (a list of worlds) and a partition, generate an arbitrary
  relation that does not relate worlds from different partition cells.
  If no cap is put on the relation, the resulting frame for each agent (after being
  closed under reflexivity and transitivity) will often be a complete graph,
  which is uninteresting. Therefore, we limit the size of the image of each world.
-}
randomRel :: [World] -> Partition -> Gen Relation
randomRel [] _ = return M.empty
randomRel (w:worlds) prt = do
      -- Get the unique info cell containing w.
      let wCell = S.toList $ head [c | c <- S.toList prt, w `elem` c]
      -- Cap the size of the image at 2.
      newImage <- M.singleton w . S.fromList <$>
        sublistOf wCell `suchThat` (\list -> length list < 3)
      rest <- randomRel worlds prt
      return $ M.union rest newImage

{-
  Given a space (a list of worlds) and a list of agents, generate an arbitrary
  relation for each agent. This function applies randomRel to each agent.
  Note: this function does not ensure a pre-order.
  TODO: use a map to make more efficient.
-}
randomRelMap :: [World] -> [Agent] -> M.Map Agent Partition -> Gen (M.Map Agent Relation)
randomRelMap _ [] _ = return M.empty
randomRelMap sp (a:agents) prt
  | null sp = return M.empty
  | otherwise = do
      newRel <- M.singleton a <$> randomRel sp (prt ! a)
      rest <- randomRelMap sp agents prt
      return $ M.union rest newRel

{-
  Generate an arbitrary Kripke model such that for all agents, the relations for
  soft evidence are pre-orders. The default full set of agents is "defaultAgents"
  and the default vocabulary is "defaultVocab" (both defined in Syntax).
-}
instance Arbitrary S4KripkeModel where
  arbitrary = do
    -- Limit the state space to at most 10 states.
    sp <- arbitrary `suchThat` isOfSizeBetween 1 10
    let agents = defaultAgents
    randomPrt <- randomPartMap sp (S.toList agents)
    randomRels <- randomRelMap (S.toList sp) (S.toList agents) randomPrt
    -- Ensure that all relations are pre-orders.
    let s4Rels = M.map (makeReflexive . makeTransitive) randomRels
    {-
      Add at most 2 "hidden" variables to the default vocabulary to allow states
      with the same valuation.
    -}
    numExtraVars <- choose (0,2)
    let voc = defaultVocab ++ take numExtraVars [freshp defaultVocab ..]
    randomV <- randomVal voc (S.toList sp)
    return (S4KM sp s4Rels randomPrt randomV)

{-
  Generate an arbitrary pointed Kripke model by choosing an arbitrary
  Kripke model and an arbitrary state in its state space.
-}
instance {-# OVERLAPPING #-} Arbitrary PtS4KripkeModel where
  arbitrary = do
    randomModel <- arbitrary
    w <- setElements (kspace randomModel)
    return (randomModel, w)