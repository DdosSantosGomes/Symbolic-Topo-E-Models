{-# LANGUAGE ImportQualifiedPost, ScopedTypeVariables, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module TestHelpers where

import Data.Set qualified as S
import Data.Set (Set)
import Test.QuickCheck (Arbitrary (arbitrary), Gen, vectorOf)
import qualified Data.IntMap as IntMap
import qualified Data.Map.Strict as M
import Data.DecisionDiagram.BDD hiding (restrict, restrictSet)
import SMCDEL.Language (Prp (..), Agent)

import Explicit.TopoEModels
import SetTheory (subsetOf, subsetOf1)
import Syntax (Form(..), defaultAgents, Group, ArbGroup (Arb))
import Symbolic.Semantics


{-
  Helper functions used for testing.
-}


-- Artificial new types.

-- Tuple of subset of space and corresponding model.
data SubsetTM = STM (Set Int) TopoEModel
  deriving (Eq, Show)

instance Arbitrary SubsetTM where
  arbitrary = do
    (tm :: TopoEModel) <- arbitrary
    subset <- subsetOf (space tm)
    return (STM subset tm)

-- Tuple of two subsets of space and corresponding model.
data SSubsetTM = SSTM (Set Int) (Set Int) TopoEModel
  deriving (Eq, Show)

instance Arbitrary SSubsetTM where
  arbitrary = do
    (tm :: TopoEModel) <- arbitrary
    subset1 <- subsetOf (space tm)
    subset2 <- subsetOf (space tm)
    return (SSTM subset1 subset2 tm)

-- Tuple (GG group subgroup) such that subgroup is a nonempty subset of group.
data TwoGroups = GG ArbGroup ArbGroup
  deriving (Eq, Show)

instance Arbitrary TwoGroups where
  arbitrary = do
    ((Arb ags1) :: ArbGroup) <- arbitrary
    ((Arb ags2) :: ArbGroup) <- Arb <$> subsetOf1 ags1
    return $ GG (Arb ags1) (Arb ags2)

{-
  Tuple (GGG group subgroup subsubgroup). Since the Arbitrary instance of ArbGroup
  ensures a nonempty subset of defaultAgents (which is also nonempty), a nonempty
  subgroup and subsubgroup are guaranteed to exist.
-}
data ThreeGroups = GGG ArbGroup ArbGroup ArbGroup
  deriving (Eq, Show)

instance Arbitrary ThreeGroups where
  arbitrary = do
    ((Arb ags1) :: ArbGroup) <- arbitrary
    ((Arb ags2) :: ArbGroup) <- Arb <$> subsetOf1 ags1
    ((Arb ags3) :: ArbGroup) <- Arb <$> subsetOf1 ags2
    return $ GGG (Arb ags1) (Arb ags2) (Arb ags3)

-- Generator for n arbitrary formulas. Used for checking the BDK axiom.
formList :: Int -> Gen [Form]
formList n = vectorOf n arbitrary

{-
  List of tuples of subgroups and formulas over the powerset of a supergroup.
  Used for checking the BDK axiom.
-}
data GFPair = GF [(Group, Form)]
  deriving (Eq, Show)

instance Arbitrary GFPair where
  arbitrary = do
    supergroup <- subsetOf1 defaultAgents
    let groups = (S.delete S.empty . S.powerSet) supergroup
    let n = length groups
    forms <- formList n
    let l = zip (S.toList groups) forms
    return (GF l)

--The powerset of agents.
allSubGroups :: [Group]
allSubGroups = S.toList $ S.powerSet defaultAgents

-- S4 axioms.

kAxiom :: Group -> Form
kAxiom ags = Impl
  (Box ags (Impl (PrpF (P 1)) (PrpF (P 2))))
  (Impl (Box ags (PrpF (P 1))) (Box ags (PrpF (P 2))))

tAxiom :: Group -> Form
tAxiom ags = Impl (PrpF (P 1)) (Dia ags (PrpF (P 1)))

fourAxiom :: Group -> Form
fourAxiom ags = Impl (Dia ags (Dia ags (PrpF (P 1)))) (Dia ags (PrpF (P 1)))

{-
  Simple topo-e-model example with two agents, three worlds, two info cells
  per agent.
-}

alice,bob :: Agent
alice = "Alice"
bob = "Bob"

singleAlice,singleBob :: Group
singleAlice = S.singleton "Alice"
singleBob = S.singleton "Bob"

spaceAB :: Set Int
spaceAB = S.fromList [1, 2, 3]

subbasisA,subbasisB :: Subbasis
subbasisA = S.fromList [ S.fromList [1]
                       , S.fromList [1,2]
                       , S.fromList [3]
                       , S.fromList [1,2,3]
                       ]
subbasisB = S.fromList [ S.fromList [1]
                       , S.fromList [2,3]
                       , S.fromList [3]
                       , S.fromList [1,2,3]
                       ]

subbMap :: M.Map Agent Subbasis
subbMap = M.fromList [(alice, subbasisA), (bob, subbasisB)]

partA,partB :: Partition
partA = S.fromList [S.fromList [1,2], S.fromList [3]]
partB = S.fromList [S.fromList [1], S.fromList [2,3]]

partMap :: M.Map Agent Partition
partMap = M.fromList [(alice, partA), (bob, partB)]

valAB :: Valuation
valAB = IntMap.fromList [ (1, M.fromList [(P 0, True), (P 1, True), (P 2, False)])
                        , (2, M.fromList [(P 0, False), (P 1, True), (P 2, False)])
                        , (3, M.fromList [(P 0, False), (P 1, False), (P 2, False)])
                        ]

tmAB :: TopoEModel
tmAB = TopoEModel spaceAB subbMap partMap valAB

-- Simple symbolic topo-structure example with one agent, three worlds, two info cells.

myVocab :: [Prp]
myVocab = [P 1, P 2, P 3, P 4, P 5, P 6]

myEvidence :: [Prp]
myEvidence = [P 1, P 2]

myPartCells :: [Prp]
myPartCells = [P 5, P 6]

myPartMap :: M.Map Agent [Prp]
myPartMap = M.fromList [("alice", myPartCells)]

myEvMap :: M.Map Agent [Prp]
myEvMap = M.fromList [("alice", myEvidence)]

myStatelaw :: Bdd
myStatelaw = conSet [ dis (var 1) (var 2)
                    , equ (neg $ var 2) (var 5), equ (var 2) (var 6)
                    , equ (var 3) (var 5)
                    , equ (var 4) (var 6)
                    ]

myStm :: SymTopoEModel
myStm = SymTEM myVocab myStatelaw myEvMap myPartMap

alicePart :: [Prp]
alicePart = obs myStm M.! "alice"

thetaImpliesPart :: Bdd
thetaImpliesPart = imp myStatelaw (xorSet (map (var . fromEnum) myPartCells))

thetaImpliesTop :: Bdd
thetaImpliesTop = imp myStatelaw top