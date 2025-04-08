{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}

module Symbolic.Semantics where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Map.Strict ((!))
import qualified Data.IntMap
import Data.DecisionDiagram.BDD hiding (existsSet,restrict,restrictSet,lfp)
import qualified Data.DecisionDiagram.BDD
import qualified Data.IntSet
import Data.List ((\\),sort, union)
import Test.QuickCheck hiding (forAll)
import SMCDEL.Language
  ( Prp (..)
  , Agent
  , Pointed
  , freshp
  )

import Explicit.Semantics (Semantics, (|=))
import Syntax
  ( Form (..)
  , simplify
  , BF (..)
  , randomBFWith
  , defaultVocab
  , defaultAgents
  , Group
  )
import Explicit.TopoEModels (filterMapOnGroup)


{-
  Semantics on the symbolic representation of topo-e-models.
  Defined on formulas of type Form (defined in Syntax).
-}


{-
  Renaming functions from `decision-diagrams` to be like HasCacBDD.
  Copied from SMCDEL.Symbolic.S5_DD.
  TODO: import instead.
-}


type Bdd = BDD AscOrder

top, bot :: Bdd
top = true
bot = false
neg :: Bdd -> Bdd
neg = notB

con, dis, imp, equ :: Bdd -> Bdd -> Bdd
con = (Data.DecisionDiagram.BDD..&&.)
dis = (Data.DecisionDiagram.BDD..||.)
imp = (Data.DecisionDiagram.BDD..=>.)
equ = (Data.DecisionDiagram.BDD..<=>.)
conSet, disSet, xorSet :: [Bdd] -> Bdd
conSet = andB
disSet = orB
xorSet [] = bot
xorSet (b:bs) = foldl xor b bs

forallSet, existsSet :: [Int] -> Bdd -> Bdd
forallSet l = forAllSet (Data.IntSet.fromList l)
existsSet l = Data.DecisionDiagram.BDD.existsSet (Data.IntSet.fromList l)

allSatsWith :: [Int] -> Bdd -> [[(Int,Bool)]]
allSatsWith ints = map Data.IntMap.toList . allSatComplete (Data.IntSet.fromList ints)

restrict :: Bdd -> (Int,Bool) -> Bdd
restrict b (k,bit) = Data.DecisionDiagram.BDD.restrict k bit b

restrictSet :: Bdd -> [(Int,Bool)] -> Bdd
restrictSet b ass = Data.DecisionDiagram.BDD.restrictSet (Data.IntMap.fromList ass) b

formOf :: Bdd -> Form
formOf = simplify . formOf' where
  formOf' :: Bdd -> Form
  formOf' (Leaf False) = Bot
  formOf' (Leaf True) = Top
  formOf' (Branch n (Leaf True)  (Leaf False)) = PrpF (P n)
  formOf' (Branch n (Leaf False) (Leaf True)) = Neg $ PrpF (P n)
  formOf' (Branch n (Leaf True) right) = Disj [ PrpF (P n), formOf' right ]
  formOf' (Branch n (Leaf False) right) = Conj [ Neg $ PrpF (P n), formOf' right ]
  formOf' (Branch n left (Leaf True)) = Disj [ Neg $ PrpF (P n), formOf' left ]
  formOf' (Branch n left (Leaf False)) = Conj [ PrpF (P n), formOf' left ]
  formOf' (Branch n left right) =
    Disj [ Conj [ PrpF (P n), formOf' left ] ,
            Conj [ Neg $ PrpF (P n), formOf' right ] ]


{-
  A symbolic representation of topo-e-models, including arbitrary model generation.
-}

{-
  A symbolic representation of topo-e-models.
  - The vocabulary includes the fresh propositions for evidence and observables.
  - The state law describes the valuation of the entire model, including the
    truth values of evidence and observables.
  - The evidence is the symbolic representation of soft evidence. It is a map
    from agents to (fresh props of) their evidence.
  - The observables are the symbolic representation of partitions. They are
    represented by a map from agents to (fresh props of) their info cells.

  We assume for efficiency that evidence and observables are disjoint; however,
  if they are not, it doesn't influence the truth and validity of formulas.

  TODO: rename to SymStruct to avoid confusion with topo-e-models.
-}
data SymTopoEModel = SymTEM
  { vocab     :: [Prp]               -- Vocabulary
  , theta     :: Bdd                 -- State law
  , evidence  :: M.Map Agent [Prp]   -- Evidence
  , obs       :: M.Map Agent [Prp]   -- Observables
  } deriving (Eq, Show)

-- A state is a list of propositional variables.
type State = [Prp]

instance Pointed SymTopoEModel State
type PtSymTopoEModel = (SymTopoEModel, State)

{-
  Given a group of agents and a observables (resp. evidence) map, return the
  union of all individual observables (resp. evidence) of the group members.
-}
evOrObsOfGroup :: Group -> M.Map Agent [Prp] -> [Prp]
evOrObsOfGroup ags evOrObs = foldr union [] (filterMapOnGroup ags evOrObs)

{-
  Boolean translation: given a formula, compute a BDD that is equivalent to that
  formula, relative to the passed symbolic topo-structure.
-}
bddOf :: SymTopoEModel -> Form -> Bdd
bddOf _   Top          = top
bddOf _   Bot          = bot
bddOf _   (PrpF (P n)) = var n
bddOf stm (Neg f)      = neg $ bddOf stm f
bddOf stm (Conj fs)    = conSet $ map (bddOf stm) fs
bddOf stm (Disj fs)    = disSet $ map (bddOf stm) fs
bddOf stm (Impl f g)   = imp (bddOf stm f) (bddOf stm g)
{-
  Box ags f is true at x, if the intersection of the factive subbasic evidence
  of the group ags at x supports f. We access the factive evidence using boolean
  quantification over the fresh variables that represent the pieces of evidence.
-}
bddOf stm (Box ags f) = forallSet evPrime $ imp evAtState evImpliesf
  where
    -- Define E_I and copied evidence E_I'.
    ev         = map fromEnum $ evOrObsOfGroup ags (evidence stm)
    evPrime    = map fromEnum $ take (length ev) [freshp (vocab stm) ..]
    -- Define a map from E_I -> E_I'.
    primeMap   = Data.IntMap.fromList $ zip ev evPrime
    -- Fix truth values for e_i' in E_I' s.t. corresp. e_i are true at current state.
    evAtState  = conSet [equ (var $ primeMap Data.IntMap.! e) (var e) | e <- ev]
    -- Accept those states that satisfy e_i for all fixed e_i'.
    stateSatEv = conSet [imp (var $ primeMap Data.IntMap.! e) (var e) | e <- ev]
    -- Range over other states within partition cell.
    otherps    = map fromEnum $ vocab stm \\ evOrObsOfGroup ags (obs stm)
    -- Check that at these other states, the evidence and theta together imply f.
    evImpliesf = forallSet otherps $ imp (con stateSatEv (theta stm)) (bddOf stm f)
{-
  Forall ags f is true at x, if the unique info cell of the group that contains
  x supports f. We access the other states in the cell using boolean
  quantification over the fresh variables that represent the observables.
-}
bddOf stm (Forall ags f) = forallSet otherps $ imp (theta stm) (bddOf stm f) where
  -- Range over other states within partition cell.
  otherps = map fromEnum $ vocab stm \\ evOrObsOfGroup ags (obs stm)
bddOf stm (Dia ags f) = neg $ bddOf stm (Box ags $ Neg f)
bddOf stm (B ags f) = forallSet otherps $ imp (theta stm) (bddOf stm $ Dia ags $ Box ags f) where
  otherps = map fromEnum $ vocab stm \\ evOrObsOfGroup ags (obs stm)
bddOf stm (K ags f)   = con (bddOf stm $ Box ags f) (bddOf stm $ B ags f)

{-
  Given an instance of Form that is boolean, compute its BDD.
  Used to generate arbitrary state laws.
  Adapted from SMCDEL.S5_DD.
-}
boolBddOf :: Form -> Bdd
boolBddOf Top          = top
boolBddOf Bot          = bot
boolBddOf (PrpF (P n)) = var n
boolBddOf (Neg f)      = neg $ boolBddOf f
boolBddOf (Conj fs)    = conSet $ map boolBddOf fs
boolBddOf (Disj fs)    = disSet $ map boolBddOf fs
boolBddOf (Impl f g)   = imp (boolBddOf f) (boolBddOf g)
boolBddOf _            = error "boolBddOf failed: Not a boolean formula."

{-
  Validity of Form on symbolic topo-structures. A formula f is valid on a passed
  symbolic topo-structure if the BDD of the implication
    statelaw -> f
  is equal to Top.
-}
validViaBdd :: SymTopoEModel -> Form -> Bool
validViaBdd stm f = top == imp (theta stm) (bddOf stm f)

{-
  Truth of Form on pointed symbolic topo-structures. A formula f is
  true at (F,x) if the restriction of the BDD of f with the valuation at x
  results in a BDD equal to Top. If the resulting BDD is equal to Bot, then f
  is not true. An error is returned in case of a restriction with an incomplete
  valuation.
-}
evalViaBdd :: PtSymTopoEModel -> Form -> Bool
evalViaBdd (stm, x) f = let
    bdd   = bddOf stm f
    b     = restrictSet bdd props
    props = [(n, P n `elem` x) | (P n) <- vocab stm]
  in
    case (b == top, b == bot) of
      (True, _) -> True
      (_, True) -> False
      _         -> error $ "evalViaBdd failed: Composite BDD leftover!\n"
        ++ "  stm:   " ++ show stm ++ "\n"
        ++ "  state: " ++ show x ++ "\n"
        ++ "  form:  " ++ show f ++ "\n"
        ++ "  bdd:   " ++ show bdd ++ "\n"
        ++ "  props: " ++ show props ++ "\n"
        ++ "  b:     " ++ show b ++ "\n"


instance Semantics SymTopoEModel where
  (|=) = validViaBdd


instance Semantics PtSymTopoEModel where
  (|=) = evalViaBdd


-- Conditions for a SymTopoEModel to represent a valid topological evidence model.


-- Check whether given SymTopoEModel has lawful partitions
hasLawfulSymPartForAgent :: Agent -> SymTopoEModel -> Bool
hasLawfulSymPartForAgent i stm =
  -- Cells of passed partition should be disjoint.
  and [ mtlyIncons c1 c2 | c1 <- iPart
                         , c2 <- iPart
                         , c1 /= c2
      ]
  -- State law should imply disjunction of all cells in the partition.
  && imp (theta stm) (disSet $ map var iPart) == top
    where
      iPart = map fromEnum (obs stm ! i)
      -- Define mutual inconsistency relative to state law.
      mtlyIncons p q = restrictSet (theta stm) [(p, True), (q, True)] == bot

{-
  Equivalent function, used for testing. Produces an output specifying which
  conditions fail in case of a SymTopoEModel that is not a symb. topo-structure.
-}
hasLawfulSymPartForAgent' :: Agent -> SymTopoEModel -> [Bool]
hasLawfulSymPartForAgent' i stm = [
  and [ mtlyIncons c1 c2 | c1 <- iPart
                         , c2 <- iPart
                         , c1 /= c2
      ]
  , imp (theta stm) (disSet $ map var iPart) == top ]
    where
      iPart = map fromEnum (obs stm ! i)
      mtlyIncons p q = restrictSet (theta stm) [(p, True), (q, True)] == bot

-- Check whether a given SymTopoEModel represents a valid symbolic topo-e-model.
isSymTopoEvidenceModel :: SymTopoEModel -> Bool
isSymTopoEvidenceModel stm =
  -- State law is consistent.
  theta stm /= bot
  -- Has lawful partitions.
  && and [hasLawfulSymPartForAgent i stm | i <- M.keys (obs stm)]
  -- Union of subbasis is full space for each agent.
  && and [unionOfSbbIsSpace i | i <- M.keys (obs stm)]
  -- All evidence is consistent with state law.
  && all propsAreConsistent (M.elems $ evidence stm)
  -- Every information cell is nonempty.
  && all propsAreConsistent (M.elems $ obs stm)
    where
      -- Define consistency relative to state law.
      propsAreConsistent = all ((\p -> restrict (theta stm) (p, True) /= bot) . fromEnum)
      unionOfSbbIsSpace i = imp (theta stm) (disSet $ map var $ iEv i) == top
      iEv i = map fromEnum (evidence stm ! i)

{-
  Similar function, used for testing specific conditions. Produces an output
  specifying which conditions fail in case of a SymTopoEModel that is not a
  symb. topo-structure.
-}
isSymTopoEvidenceModel' :: SymTopoEModel -> (Bool, [[Bool]], Bool, [Bool])
isSymTopoEvidenceModel' stm = (
  theta stm /= bot
  -- Has lawful partitions.
  , [hasLawfulSymPartForAgent' i stm | i <- M.keys (obs stm)]
  -- All evidence is consistent with state law.
  , all propsAreConsistent (M.elems $ evidence stm)
  -- Every information cell is nonempty.
  , [propsAreConsistent (obs stm ! i) | i <- M.keys (obs stm)])
    where
      propsAreConsistent = all ((\p -> restrict (theta stm) (p, True) /= bot) . fromEnum)


-- Arbitrary SymTopoEModel generation.


{-
  Given a list of propositional variables and a list of agents, allocate a subset
  of the evidence to each agent. Multiple agents can possess the same piece of
  evidence, but every piece of evidence is possessed by at least one agent.
-}
divideEvidence :: [Prp] -> [Agent] -> Gen (M.Map Agent [Prp])
divideEvidence ev = divHelper ev ev
  where
    divHelper _ _         []         = pure M.empty
    divHelper _ remainder [a]        = return $ M.singleton a remainder
    divHelper e remainder (a:agents) = do
      eOfAgent <- sublistOf e
      let r = remainder \\ eOfAgent
      M.insert a eOfAgent <$> divHelper e r agents

-- For each agent, assign a list of fresh variables (given max size maxC)
-- Each observable represents a cell

{-
  Given an initial vocabulary, a list of agents, and a maximum of cells per agent,
  allocate an arbitrary subset of observables to each agent. Observables are
  represented by variables that are fresh w.r.t. the vocabulary.
-}
randomPart :: [Prp] -> [Agent] -> Int -> Gen (M.Map Agent [Prp])
randomPart _   []         _    = return M.empty
randomPart voc (a:agents) maxC = do
  numCells <- choose (1, maxC)
  let cellVars = take numCells [freshp voc ..]
  -- Update the vocabulary after each allocation.
  let newVoc = voc ++ cellVars
  M.insert a cellVars <$> randomPart newVoc agents maxC

-- Adapted from Arbitrary BelStruct (SMCDEL.K)

{-
  Generate an arbitrary symbolic topo-structure. The default full set of agents
  is "defaultAgents" and the default vocabulary is "defaultVocab" (both defined
  in Syntax).
-}
instance Arbitrary SymTopoEModel where
  arbitrary = do
    -- Vocabulary.
    numExtraVars <- choose (0,1)
    let voc = defaultVocab ++ take numExtraVars [freshp defaultVocab ..]

    -- Evidence props (default maximum is 1 times nr of agents).
    evVars <- do
      let maxEv = 1 * length defaultAgents
      numEv <- choose (1, maxEv)
      return $ take numEv [freshp voc ..]
    -- Observed evidence per agent.
    evMap <- divideEvidence evVars (S.toList defaultAgents)

    {-
      Add one piece of evidence "fullSpace" describing the full space, to each
      evidence set to ensure that the union of each subbasis is the full space.
    -}
    let fullSpace = freshp (voc ++ evVars)
    let vocWithEv = fullSpace : voc ++ evVars
    let newEvMap = M.map (fullSpace :) evMap

    -- Partitions per agent (default maximum of cells per partition is 3).
    let maxCells = 3
    partMap <- randomPart vocWithEv (S.toList defaultAgents) maxCells
    let vocWithParts = sort $ foldr (++) vocWithEv (M.elems partMap)

    -- State law (consistent with partitions) and corresponding BDD.
    let cells i = map fromEnum (partMap ! i)
    let evOf i = map fromEnum (newEvMap ! i)
    -- Enforce that valuation on observables constitutes a lawful partition.
    let oneCellPerAg = conSet [disSet (map var $ cells i) | i <- S.toList defaultAgents]
    let onlyOneCellPerAg i = conSet [ dis (neg $ var c1) (neg $ var c2) | c1 <- cells i
                                                                        , c2 <- cells i
                                                                        , c1 /= c2
                                    ]
    let partLaw = con oneCellPerAg (conSet [onlyOneCellPerAg i | i <- S.toList defaultAgents])
    -- Avoid redundancies: ensure that partitions and evidence are consistent.
    let simpPart b i = and [restrict b (c, True) /= bot | c <- cells i]
    let simpEv b i = and [restrict b (c, True) /= bot | c <- evOf i]
    let simpAll b = all (\i -> simpPart b i && simpEv b i) defaultAgents
     -- Combine all conditions into one state law. Ensure that fullSpace is valid.
    let lawBdd bf = conSet [boolBddOf bf, partLaw, (var . fromEnum) fullSpace]
    (BF statelaw) <-
      sized (randomBFWith vocWithParts) `suchThat` \(BF b) ->
        simpAll (lawBdd b)
    let stateBdd = lawBdd statelaw

    return $ SymTEM vocWithParts stateBdd newEvMap partMap

-- Given a symbolic topo-structure, generate a random state of the structure.
randomState :: SymTopoEModel -> Gen State
randomState stm = sublistOf v `suchThat` isSatAss where
  v = vocab stm
  ass s = [(fromEnum p, True) | p <- s] ++ [(fromEnum p, False) | p <- v \\ s]
  isSatAss s = restrictSet (theta stm) (ass s) /= bot

{-
  Generate an arbitrary pointed symbolic topo-structure by choosing an arbitrary
  topo-structure and an arbitrary state of the structure. Uses randomState.
-}
instance {-# OVERLAPPING #-} Arbitrary PtSymTopoEModel where
  arbitrary = do
    stm <- arbitrary
    (s :: [Prp]) <- randomState stm
    return (stm, s)