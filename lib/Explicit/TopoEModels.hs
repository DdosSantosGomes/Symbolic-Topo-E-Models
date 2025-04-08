{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Explicit.TopoEModels where

import qualified Data.Set as S
import Data.Set (Set, isSubsetOf, singleton, union, (\\))
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Test.QuickCheck
  ( Arbitrary (arbitrary)
  , Gen
  , suchThat
  , sublistOf
  )
import SMCDEL.Language
  ( Prp (..)
  , Agent
  , Pointed
  )

import SetTheory
  ( arbIntersection
  , closeUnderIntersection
  , closeUnderUnion
  , isOfSizeBetween
  , setElements
  , setOf1
  , subsetOf
  , World
  )
import Syntax (defaultVocab, defaultAgents, Group)


{-
  An explicit representation of topo-e-models, including arbitrary model generation.
-}


{-
  Valuations map worlds to maps from propositional variables to boolean values.
  Subbases, partitions, and topologies have the same type: a set of sets of worlds.
  Instances of Partition are not forced to be valid partitions, and topologies
  are not forced to be closed under union and intersection.
-}
type Valuation = IntMap (M.Map Prp Bool)
type Subbasis = Set (Set World)
type Partition = Set (Set World)
type Topology = Set (Set World)

{-
  An explicit (topological) representation of topo-e-models. We assume that
  subbasis and partition (soft and hard evidence) are disjoint for each agent in
  the semantics, which is not enforced by this type. A representation that does
  not satisfy this property is less efficient. However, since the representations
  are equivalent, overlap of evidence does not influence the truth and validity
  of formulas.
-}
data TopoEModel = TopoEModel
  { space :: Set World                 -- Full space
  , subb  :: M.Map Agent Subbasis      -- Map from agents to their subbases
  , part  :: M.Map Agent Partition     -- Map from agents to their partitions
  , val   :: Valuation                 -- Valuation
  } deriving (Eq, Show)

instance Pointed TopoEModel World
type PtTopoEModel = (TopoEModel, World)

-- Get all agents of a given topo-e-model.
agentsOf :: TopoEModel -> Group
agentsOf = S.fromList . M.keys .subb

-- Filter a subbasis map or partition map on a given group of agents.
filterMapOnGroup :: Group -> M.Map Agent b -> M.Map Agent b
filterMapOnGroup ags = M.filterWithKey (\k _ -> k `elem` S.toList ags)

{-
  Given a group of agents, generate their topology: close the union of the join
  subbasis and group partition first under intersections, and then under unions.
-}
generateTop :: Group -> TopoEModel -> Topology
generateTop ags tm = closeUnderUnion . closeUnderIntersection $ opensWithParts where
  joinSbb = joinSubbasis ags tm
  allObs = obsOfGroup ags tm
  opensWithParts = joinSbb `union` allObs

-- Given a group of agents, compute the join subbasis (union of individual subbases).
joinSubbasis ::  Group -> TopoEModel -> Subbasis
joinSubbasis ags tm = (S.unions . S.fromList . M.elems) groupMap where
  groupMap = filterMapOnGroup ags (subb tm)

{-
  Helper function to compute the complete group partition of a group of agents.
  Given a group, return the union of individual partitions. This is not the same
  as a group partition.
-}
obsOfGroup :: Group -> TopoEModel -> Set (Set World)
obsOfGroup ags tm = (S.unions . S.fromList . M.elems) groupMap where
  groupMap = filterMapOnGroup ags (part tm)

{-
  Group partition for a given group of agents ags = {1,...,n}, obtained by
  intersecting all tuples (pi_1,...,pi_n) s.t. each pi is a partition cell for
  agent i. To compute a particular cell in this partition that contains some state
  x, use the "cellOfStateTM" function (defined below) instead.
-}
groupPart :: Group -> TopoEModel -> Partition
groupPart ags tm = arbIntersection (S.powerSet allObs) where
  allObs = obsOfGroup ags tm

{-
  Given state x, a group of agents, and a topo-e-model, compute their unique info
  cell containing x. Note: this function is unsafe. It assumes that "part tm" is
  a valid partition, s.t. "cellOf i" is the head of a singleton list.
  To compute the complete group partition, use the "groupPart"
  function (defined above) instead.
-}
cellOfStateTM :: World -> Group -> TopoEModel -> Set World
cellOfStateTM x ags tm = arbIntersection allInfoCells where
  cellOf i =  head [c | c <- S.toList (part tm ! i), x `elem` c]
  allInfoCells = S.fromList [cellOf i | i <- S.toList ags]

-- Return the vocabulary of a topo-e-model.
vocabOf :: TopoEModel -> [Prp]
vocabOf tm = M.keys $ head (IntMap.elems (val tm))

-- Check if a given cell is open in the topology of a given group.
isOpenForGroup :: Set World -> Group -> TopoEModel -> Bool
isOpenForGroup set ags tm = set `elem` generateTop ags tm

{-
  Given a state, group, and topo-e-model, return the open neighbourhoods of that
  state for that group.
-}
sbOpenNbdsOfState :: World -> Group -> TopoEModel -> Set (Set World)
sbOpenNbdsOfState x ags tm = S.filter (x `elem`) (joinSubbasis ags tm)

-- Check if a given cell is closed in the topology of a given group.
isClosedForGroup :: Set World -> Group -> TopoEModel -> Bool
isClosedForGroup set ags tm = space tm \\ set `elem` generateTop ags tm

-- Given a group and a topo-e-model, return the closed sets for that group.
closedsForGroup :: Group -> TopoEModel -> Set (Set World)
closedsForGroup ags tm = S.map (space tm \\) (generateTop ags tm)

--  Given a group and a topo-e-model, return the clopen sets for that group.
isClopenForGroup :: Set World -> Group -> TopoEModel -> Bool
isClopenForGroup set ags tm = isOpenForGroup set ags tm && isClosedForGroup set ags tm

-- Given a set A, group, and topo-e-model, return Int(A) for the group.
interiorForGroup :: Set World -> Group -> TopoEModel -> Set World
interiorForGroup set ags tm = S.unions opensBelowSet where
  opensBelowSet = S.filter (`isSubsetOf` set) (generateTop ags tm)

-- Given a set A, group, and topo-e-model, return Cl(A) for the group.
closureForGroup :: Set World -> Group -> TopoEModel -> Set World
closureForGroup set ags tm = arbIntersection closedsAboveSet
  where
    closedsWithParts = S.map (space tm \\) (generateTop ags tm)
    closedsAboveSet = S.filter (set `isSubsetOf`) closedsWithParts

{-
  Check if a given set of sets of worlds is a basis for a given topology, i.e.
  if closure under union results in the given topology.
-}
isBasisFor :: Set (Set World) -> Topology -> Bool
isBasisFor sets top = closeUnderUnion sets == top

{-
  Check  if a given set of sets of worlds is a subbasis for a given topology, i.e.
  if closure under intersection results in a basis for the given topology.
-}
isSubbasisFor :: Set (Set World) -> Topology -> Bool
isSubbasisFor sets top = closeUnderIntersection sets `isBasisFor` top


-- Conditions for an instance of TopoEModel to represent a valid topo-e-model.


-- Given an agent i, check if the partition of i in the given topo-e-model is valid.
hasLawfulPartForAgent :: Agent -> TopoEModel -> [Bool]
hasLawfulPartForAgent i tm =
  -- Passed partition should partition the space into disjoint sets.
  [ and [ S.disjoint s1 s2 | s1 <- S.toList iPart
                           , s2 <- S.toList iPart
                           , s1 /= s2
        ]
  -- Union of partition cells should equial passed space.
  , S.unions iPart == space tm
  ] where
    iPart = part tm ! i

{-
  Given an agent i, check if the topology for i in the given topo-e-model is
  valid. According to the single-agent definition of a subbasis, it should include
  the full set as an element. In the multi-agent case, this information becomes
  redundant due to the partitions; therefore, we do not require it.
-}
hasLawfulTopoForAgent :: Agent -> TopoEModel -> [Bool]
hasLawfulTopoForAgent i tm =
  -- Passed space should not be empty.
  [ space tm /= S.empty
  -- Union of passed subbasis should equal passed space.
  , S.unions iSubb == space tm
  -- Passed subbasis should not include the empty set.
  ,  S.empty `notElem` iSubb
  ] where
    iSubb = subb tm ! i

{-
  Given a TopoEModel, check whether it is a lawful topological evidence model.
  A TopoEModel is a topological evidence model if for all agents,
    (1) it describes a lawful partition, and
    (2) it describes a lawful combination of subbasis and topology.
-}
isTopoEvidenceModel :: TopoEModel -> Bool
isTopoEvidenceModel tm = and
  [ and (hasLawfulPartForAgent i tm) &&
    and (hasLawfulTopoForAgent i tm) | i <- M.keys (subb tm)
  ]

{-
  Equivalent function, used for testing. Produces an output specifying which
  conditions fail in case of a TopoEModel that is not a topological evidence model.
-}
isTopoEvidenceModel' :: TopoEModel -> [([Bool],[Bool])]
isTopoEvidenceModel' tm =
  [(hasLawfulPartForAgent i tm, hasLawfulTopoForAgent i tm) | i <- M.keys (subb tm)]


-- Arbitrary TopoEModel generation


{-
  Given a state space, generate an arbitrary subbasis. Ensures that the union of
  the subbasis is the full space, and that it does not contain the empty set as
  an element.
-}
randomSubb :: Set World -> Gen Subbasis
randomSubb sp = do
  sb <-
    -- Generate a set of at most 3 nonempty subsets of the space.
    let oneSet = (setOf1 (setElements sp) `suchThat` isOfSizeBetween 0 3)
      in setOf1 oneSet `suchThat` isOfSizeBetween 0 3
  -- Define the set of all points not included in the subbasis.
  let leftovers = sp \\ S.unions sb
  {-
    Add the leftovers as an element. The leftovers might be empty:
    delete the empty set if it is now an element.
    TODO: make more efficient.
  -}
  return $ S.delete S.empty (S.insert leftovers sb)

{-
  Given a state space and a list of agents, generate a subbasis for each agent.
  This function applies randomSubb to each agent.
  TODO: use a map to make more efficient.
-}
randomSubbMap :: Set World -> [Agent] -> Gen (M.Map Agent Subbasis)
randomSubbMap _ [] = return M.empty
randomSubbMap sp (agent:agents)
  | null sp = return M.empty
  | otherwise = do
      newSubb <- M.singleton agent <$> randomSubb sp
      rest <- randomSubbMap sp agents
      return $ M.union rest newSubb

{-
  Given a state space, generate an arbitrary partition. Ensures that the cells
  are disjoint and that the union of cells is the full space.
-}
randomPart :: Set World -> Gen Partition
randomPart sp = do
  subset <- subsetOf sp
  let remainder = sp \\ subset
  rest <- if not (null remainder) then randomPart remainder
    else subsetOf S.empty
  return $ S.delete S.empty (singleton subset `union` rest)

{-
  Given a state space and a list of agents, generate a partition for each agent.
  This function applies randomPart to each agent.
  TODO: use a map to make more efficient.
-}
randomPartMap :: Set World -> [Agent] -> Gen (M.Map Agent Partition)
randomPartMap _ [] = return M.empty
randomPartMap sp (agent:agents)
  | null sp = return M.empty
  | otherwise = do
      newPart <- M.singleton agent <$> randomPart sp
      rest <- randomPartMap sp agents
      return $ M.union rest newPart

{-
  Given a list of propositional variables and a list of worlds, assign an
  arbitrary valuation to each world.
  TODO: use a map to make more efficient.
-}
randomVal :: [Prp] -> [World] -> Gen Valuation
randomVal _ [] = return IntMap.empty
randomVal ps (world:worlds) = do
  trueP <- sublistOf ps
  let newVal = IntMap.singleton world (M.fromList [(p, p `elem` trueP) | p <- ps])
  rest <- randomVal ps worlds
  return $ IntMap.union rest newVal

{-
  Generate an arbitrary topo-e-model. The default full set of agents is
  "defaultAgents" and the default vocabulary is "defaultVocab" (both defined
  in Syntax).
-}
instance Arbitrary TopoEModel where
  arbitrary = do
    -- Limit the state space to at most 10 states.
    (sp :: Set Int) <- arbitrary `suchThat` isOfSizeBetween 1 10
    let agents = S.toList defaultAgents
    parts    <- randomPartMap sp agents
    subbases <- randomSubbMap sp agents
    v <- randomVal defaultVocab (S.toList sp)
    return (TopoEModel sp subbases parts v)

{-
  Generate an arbitrary pointed topo-e-model by choosing an arbitrary
  topo-e-model and an arbitrary state in its state space.
-}
instance {-# OVERLAPPING #-} Arbitrary PtTopoEModel where
  arbitrary = do
    tm <- arbitrary
    (x :: Int) <- setElements (space tm)
    return (tm, x)