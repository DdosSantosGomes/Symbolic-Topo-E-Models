module ModelConversion where

import qualified Data.Set as S
import Data.Set (singleton, Set)
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import qualified Data.IntMap as IntMap
import Control.Arrow (first)
import Data.DecisionDiagram.BDD (var)
import Data.List ((\\), sort, elemIndex)
import Data.Containers.ListUtils (nubOrd)
import SMCDEL.Internal.Help (groupSortWith, powerset)
import SMCDEL.Language (Agent, Prp (..), freshp)

import Explicit.KripkeModels
  (PtS4KripkeModel, S4KripkeModel(..))
import Explicit.TopoEModels
  ( PtTopoEModel
  , TopoEModel (..)
  , Subbasis
  , closureForGroup
  , cellOfStateTM
  , Valuation
  , joinSubbasis
  , obsOfGroup
  , vocabOf
  , agentsOf
  )
import Symbolic.Semantics
    ( State
    , SymTopoEModel(..)
    , Bdd
    , allSatsWith
    , PtSymTopoEModel
    , disSet
    , conSet
    , neg
    )
import SetTheory (Relation, World)
import Data.Maybe (fromJust)

{-
  Maps between explicit Kripke models and explicit topo-e-models.
-}


{-
  Given an explicit Kripke model and agent i, construct a subbasis for i by taking
  the set of all upsets generated by singletons w.r.t. i's accessibility relation:
    {\uparrow_i {x} | x\in X}.
-}
getSubbForAgent :: S4KripkeModel -> Agent -> Subbasis
getSubbForAgent km i = S.fromList upsets where
  upsets = [rel km ! i ! x | x <- S.toList (kspace km)]

{-
  Convert an explicit Kripke model to an explicit topo-e-model.
  Uses getSubbForAgent.
-}
expKripkeToExpTopo :: S4KripkeModel -> TopoEModel
expKripkeToExpTopo km = TopoEModel (kspace km) sbb parts (kval km)
  where
    agents = M.keys (rel km)
    parts = kpart km
    sbb = M.fromList [(i, getSubbForAgent km i) | i <- agents]


{-
  Given an explicit topo-e-model and agent, construct the spec. pre-order for i.
  We have xR_i y if
    (1) x is in the closure of {y}, and
    (2) x and y are in the same info cell of i,

  TODO: make more efficient by inverting map (Cl(v) = R-1(v)).
-}
relOfAgent :: TopoEModel -> Agent -> Relation
relOfAgent tm i = M.fromList [(w, image w) | w <- spList]
  where
    single  = S.singleton
    spList  = S.toList $ space tm
    image w = S.fromList [ v | v <- S.toList $ cellOfStateTM w (single i) tm
                             , w `elem` closureForGroup (singleton v) (single i) tm
                         ]
{-
  Convert an explicit topo-e-model to an explicit Kripke model.
  Uses relOfAgent.
-}
expTopoToExpKripke :: TopoEModel -> S4KripkeModel
expTopoToExpKripke tm = S4KM (space tm) rela (part tm) (val tm)
  where
    rela = M.fromList [(i, relOfAgent tm i) | i <- M.keys $ subb tm]

{-
  Conversions for pointed models: the actual state doesn't change.
-}
expKripkeToExpTopoPt :: PtS4KripkeModel -> PtTopoEModel
expKripkeToExpTopoPt (km, x) = (expKripkeToExpTopo km, x)

expTopoToExpKripkePt :: PtTopoEModel -> PtS4KripkeModel
expTopoToExpKripkePt (tm, x) = (expTopoToExpKripke tm, x)


-- Maps from symbolic topo-structures to explicit topo-e-models.


{-
  Given vocab and state law, obtain and index all states of a knowledge structure.
  The indices will represent the worlds in the corresponding explicit topo-e-model.
  Adapted from SMCDEL.K.
-}
statesToWorlds :: [Prp] -> Bdd -> M.Map State World
statesToWorlds voc statelaw = M.fromList $ zip (map (sort . getTrues) prpsats) [0..]
  where
    bddvars = map fromEnum voc
    bddsats = allSatsWith bddvars statelaw
    prpsats = map (map (first toEnum)) bddsats
    getTrues = map fst . filter snd

{-
  Given a propositional variable and a set of indexed states (worlds), get the
  truth set of the variable, that is, all indices of worlds satisfying the
  given variable.
-}
truthSetOf :: Prp -> M.Map State World -> Set World
truthSetOf p statemap = S.fromList $ map (statemap !) satStates where
  satStates = filter (p `elem`) $ M.keys statemap

{-
  Given a set of indexed states (worlds), convert type
  M.Map Agent [Prp]           (symbolic) to
  M.Map Agent Set (Set World) (explicit).
  Used for both partition and subbasis.

  Assumes a correct input, that is, a symbolic structure where the observables
  constitute a partition for each agent.
-}
symToExpMap :: M.Map Agent [Prp] -> M.Map State World -> M.Map Agent (Set (Set World))
symToExpMap symMap statemap = M.map propsToSets symMap where
  propsToSets xs = S.fromList $ map (`truthSetOf` statemap) xs

{-
  Given a map from states (lists of true props) to worlds (indices),
  get the corresponding valuation map (mapping indices to
  maps from props to boolean values).
-}
valOf :: [Prp] -> M.Map [Prp] Int -> Valuation
valOf ps statemap = IntMap.unions $ map mapOf (M.keys statemap) where
  mapOf s = IntMap.singleton (statemap ! s) $ M.fromList [(p, p `elem` s) | p <- ps]

-- Convert a symbolic topo-structure to an explicit topo-e-model.
symTopoToExpTopo :: SymTopoEModel -> TopoEModel
symTopoToExpTopo stm = TopoEModel sp sbb prt v
  where
    statemap = statesToWorlds (vocab stm) (theta stm)
    v    = valOf (vocab stm) statemap
    sp   = S.fromList $ M.elems statemap
    sbb  = symToExpMap (evidence stm) statemap
    prt  = symToExpMap (obs stm) statemap

{-
  Conversion from pointed symbolic topo-structures to pointed topo-e-models.
  The actual state gets mapped to the corresponding world using the same function
  "statesToWorlds" that indexes all states of the structure.
-}
symTopoToExpTopoPt :: PtSymTopoEModel -> PtTopoEModel
symTopoToExpTopoPt (stm, s) = (tm, w)
  where
    symStates = statesToWorlds (vocab stm) (theta stm)
    tm = symTopoToExpTopo stm
    w = symStates ! s


-- Maps from explicit topo-e-models to symbolic topo-structures.


{-
  Given an indexing of sets of states, convert type
  M.Map Agent Set (Set World) (explicit) to
  M.Map Agent [Prp]           (symbolic).
  Used for both partition and subbasis.
-}
expToSymMap :: M.Map Agent (Set (Set World)) -> M.Map (Set World) Prp -> M.Map Agent [Prp]
expToSymMap expMap indSets = M.map setsToProps expMap where
  setsToProps = map (indSets !) . S.toList

{-
  Given a world w, a collection "expSets" of sets S of worlds (explicit), and a map from
  sets S to Prps p (symbolic), return the Prps p corresponding to the sets S such
  that w in S, that is, factive evidence from "expSets" at w.
  Used for both partition and subbasis.
-}
propsAtWorld :: World -> Set (Set World) -> M.Map (Set World) Prp -> [Prp]
propsAtWorld w expSets indSets = map (indSets !) $ S.toList factiveSets where
  factiveSets = S.filter (w `elem`) expSets

{-
  Given an explicit topo-e-model, add fresh propositions to the vocabulary to
  represent evidence and observables in the equivalent symbolic structure. Return
  the evidence and observables indexed by these fresh propositions.
-}
indexEvAndObs :: TopoEModel -> (M.Map (Set World) Prp, M.Map (Set World) Prp)
indexEvAndObs tm = (indexedEv, indexedObs)
  where
    allAgs = agentsOf tm
    totalEv = joinSubbasis allAgs tm
    totalObs = obsOfGroup allAgs tm
    evProps = take (length totalEv) [freshp (vocabOf tm) ..]
    obProps = take (length totalObs) [freshp (vocabOf tm ++ evProps) ..]
    indexedEv = M.fromList $ zip (S.toList totalEv) evProps
    indexedObs = M.fromList $ zip (S.toList totalObs) obProps

{-
  Given a world w, an explicit topo-e-model tm, and indexed evidence and observables,
  return the state in the symbolic topo-structure corresponding to w in the
  explicit topo-e-model.
-}
worldToState :: World -> TopoEModel -> M.Map (Set World) Prp -> M.Map (Set World) Prp -> State
worldToState w tm indEv indObs = pAtWorld w ++ evAtWorld w ++ obsAtWorld w
  where
    allAgs = agentsOf tm
    -- Get valuations of Prps, evidence, and observables.
    pAtWorld    v = M.keys $ M.filter id (val tm IntMap.! v)
    evAtWorld   v = propsAtWorld v (joinSubbasis allAgs tm) indEv
    obsAtWorld  v = propsAtWorld v (obsOfGroup allAgs tm) indObs

{-
  BDD that states that out of a given vocabulary qs, exactly the subset ps is true.
  Copied from SMCDEL.Translations.S5, so that it works with our type of BDD.
-}
booloutof :: [Prp] -> [Prp] -> Bdd
booloutof ps qs = conSet $
  [var n | (P n) <- ps] ++
  [neg $ var n | (P n) <- qs \\ ps]

{-
  Check whether all worlds in a given explicit topo-e-model have a distinct valuation.
  Adapted from SMCDEL.Explicit.K.
-}
distinctVal :: TopoEModel -> Bool
distinctVal tm = IntMap.size v == length (nubOrd (IntMap.elems v)) where
  v = val tm

{-
  Ensure distinct valuations for all worlds in explicit topo-e-model. Given n
  worlds with the same valuations, add log n many fresh propositional variables
  such that each world gets an updated valuation, which sets a unique subset of the
  fresh variables to true.
  Adapted from SMCDEL.Translations.K.
-}
ensureDistinctVal :: TopoEModel -> TopoEModel
ensureDistinctVal tm = if distinctVal tm then tm else newtm where
  -- Construct equivalence classes of worlds with the same valuation.
  sameVals = groupSortWith (val tm IntMap.!) (S.toList $ space tm)
  -- Define index of world w as index of the (first) occurrence of w in its equiv. class
  indexOf w = fromJust $ elemIndex w (head $ filter (elem w) sameVals)
  -- Get the number of fresh Prps that need to be added.
  numAddProps = ceiling $ logBase (2::Double) (fromIntegral $ maximum (map length sameVals) + 1)
  -- Define the fresh Prps.
  addProps = take numAddProps [freshp (vocabOf tm) ..]
  -- Based on powerset of fresh Prps and index k (of w), decide valuation for w.
  addValForIndex k = M.fromList [(p, p `elem` (reverse (powerset addProps) !! k) ) | p <- addProps]
  -- For each w, define updated valuation including fresh Prps.
  updateProps w = M.union (val tm IntMap.! w) (addValForIndex (indexOf w))
  newVal = IntMap.fromList [(w, updateProps w) | w <- IntMap.keys $ val tm]
  newtm = TopoEModel (space tm) (subb tm) (part tm) newVal

{-
  Convert an explicit topo-e-model to a symbolic topo-structure. This function is
  unsafe: it assumes that each world has a distinct valuation.
-}
expTopoToSymTopoUnsafe :: TopoEModel -> SymTopoEModel
expTopoToSymTopoUnsafe tm = SymTEM voc statelaw evMap obMap
  where
    (indexedEv, indexedObs) = indexEvAndObs tm
    evProps   = M.elems indexedEv
    obProps   = M.elems indexedObs
    voc       = vocabOf tm ++ evProps ++ obProps
    evMap     = expToSymMap (subb tm) indexedEv
    obMap     = expToSymMap (part tm) indexedObs
    stateOf w = worldToState w tm indexedEv indexedObs
    -- Define the state law from a disjunction of possible valuations.
    statelaw  = disSet [booloutof (stateOf w) voc | w <- S.toList $ space tm]

{-
  Convert an explicit topo-e-model to a symbolic topo-structure, after ensuring
  a distinct valuation for all worlds.
  Safe function.
-}
expTopoToSymTopo :: TopoEModel -> SymTopoEModel
expTopoToSymTopo tm | distinctVal tm = expTopoToSymTopoUnsafe tm
                    | otherwise      = expTopoToSymTopoUnsafe (ensureDistinctVal tm)

{-
  Conversion from pointed topo-e-models to pointed symbolic topo-structures. The
  actual world gets mapped to the corresponding state using the same function
  "worldToState" that computes all states of the structure.
-}
expTopoToSymTopoPt :: PtTopoEModel -> PtSymTopoEModel
expTopoToSymTopoPt (tm, w) = (stm, s)
  where
    newtm = ensureDistinctVal tm
    stm = expTopoToSymTopo newtm
    (indexedEv, indexedObs) = indexEvAndObs newtm
    s = worldToState w newtm indexedEv indexedObs