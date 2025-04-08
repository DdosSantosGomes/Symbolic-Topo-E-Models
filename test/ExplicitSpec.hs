{-# LANGUAGE BlockArguments, FlexibleContexts #-}

module ExplicitSpec where

import Test.Hspec (describe, it, shouldBe, Spec)
import Test.Hspec.QuickCheck (prop)
import qualified Data.Set as S
import Data.Set (Set, isSubsetOf, intersection, union)
import SMCDEL.Language (Prp (..))

import ModelConversion
  ( expTopoToExpKripke
  , expTopoToExpKripkePt
  , expKripkeToExpTopo
  , expKripkeToExpTopoPt
  )
import SetTheory
  ( makeTransitive
  , Relation
  , makeReflexive
  )
import Syntax (Form (..), ArbGroup (Arb))
import Explicit.TopoEModels
  ( TopoEModel (..)
  , PtTopoEModel
  , closureForGroup
  , interiorForGroup
  , isTopoEvidenceModel
  , closedsForGroup
  , isOpenForGroup
  , isClosedForGroup
  , generateTop
  )
import Explicit.KripkeModels
  ( S4KripkeModel (..)
  , PtS4KripkeModel
  , groupRel
  )
import Explicit.Semantics (Semantics ((|=)))
import TestHelpers
  ( SubsetTM (..)
  , SSubsetTM (SSTM)
  , tmAB
  , kAxiom
  , tAxiom
  , fourAxiom
  , singleAlice
  , singleBob
  , TwoGroups (GG)
  , ThreeGroups (GGG)
  , GFPair (..)
  )


{-
  Testing of the implementation of the explicit topo-e-model.
-}


spec :: Spec
spec = do
  describe "TopoEModel generation" $ do
    prop "Arbitrary TopoEModel is a topological evidence model" $ do
      \tm -> isTopoEvidenceModel (tm :: TopoEModel)
  describe "Kripke Model generation" $ do
    prop "Group relations in arbitrary S4 Kripke Model are reflexive and transitive" $ do
      \km (Arb ags) ->
        makeReflexive (groupRel ags (km :: S4KripkeModel) :: Relation) == groupRel ags km &&
        makeTransitive (groupRel ags (km :: S4KripkeModel) :: Relation) == groupRel ags km

  describe "Kuratowski Axioms hold for the interior operator" $ do
    prop "Int() preserves the total space" $ do
      \tm (Arb ags) ->
        interiorForGroup (space (tm :: TopoEModel)) ags tm `shouldBe` space tm
    prop "Int() is intensive" $ do
      \(STM setA tm) (Arb ags) ->
        interiorForGroup (setA :: Set Int) ags tm `isSubsetOf` setA
    prop "Int() is idempotent" $ do
      \(STM setA tm) (Arb ags) ->
        interiorForGroup (setA :: Set Int) ags tm
          `shouldBe` interiorForGroup (interiorForGroup setA ags tm) ags tm
    prop "Int() preserves binary intersections" $ do
      \(SSTM setA setB tm) (Arb ags) ->
        interiorForGroup ((setA :: Set Int) `intersection` setB) ags tm
          `shouldBe` interiorForGroup setA ags tm `intersection` interiorForGroup setB ags tm

  describe "Kuratowski Axioms hold for the closure operator" $ do
    prop "Cl() preserves the empty set" $ do
        \tm (Arb ags) ->
          closureForGroup S.empty ags (tm :: TopoEModel) `shouldBe` S.empty
    prop "Cl() is extensive" $ do
        \(STM setA tm) (Arb ags) ->
          (setA :: Set Int) `isSubsetOf` closureForGroup setA ags tm
    prop "Cl() is idempotent" $ do
         \(STM setA tm) (Arb ags) ->
          closureForGroup (setA :: Set Int) ags tm
            `shouldBe` closureForGroup (closureForGroup setA ags tm) ags tm
    prop "Cl() distributes over binary unions" $ do
         \(SSTM setA setB tm) (Arb ags) ->
          closureForGroup ((setA :: Set Int) `union` setB) ags tm
            `shouldBe` closureForGroup setA ags tm `union` closureForGroup setB ags tm

  describe "Computations on topologies" $ do
    it "Closed sets computed correctly" $ do
      let result = S.fromList [ S.fromList []
                              , S.fromList [1,2,3]
                              , S.fromList [1,2]
                              , S.fromList [2,3]
                              , S.fromList [2]
                              , S.fromList [3]
                              ]
      closedsForGroup singleAlice tmAB `shouldBe` result
    it "Opens are correctly identified" $ do
      isOpenForGroup (S.fromList [3]) singleAlice tmAB &&
        not (isOpenForGroup (S.fromList [2]) singleAlice tmAB)
    it "Closed sets are correctly identified" $ do
      isClosedForGroup (S.fromList [1]) singleBob tmAB &&
        not (isClosedForGroup (S.fromList [3]) singleBob tmAB)

  describe "Box coincides with interior" $ do
    prop "x models Box ags f iff x is in interior of f for ags" $ do
      \f ptm@(tm, x) (Arb ags) ->
        let states = S.toList $ space (tm :: TopoEModel)
            satf s = (tm, s) |= (f :: Form)
            fStates = S.fromList $ filter satf states in
        ptm |= Box ags f `shouldBe` (x `elem` interiorForGroup fStates ags tm)
  describe "Topo-e-semantics" $ do
    prop "Validates the K, T, and 4 axioms for all groups" $ do
      \tm (Arb ags) ->
        ((tm :: TopoEModel) |= kAxiom ags) &&
        (tm |= tAxiom ags) &&
        (tm |= fourAxiom ags)
    prop "Validates tautology p or not p, does not satisfy p and not p" $ do
      \tm ->
        (tm :: TopoEModel) |= Disj [PrpF (P 1), Neg $ PrpF (P 1)] &&
          not (tm |= Conj [PrpF (P 1), Neg $ PrpF (P 1)])
    prop "Validates modal tautology Dia p or not Dia p for all groups" $ do
      \tm (Arb ags) ->
        (tm :: TopoEModel) |= Disj [Dia ags $ PrpF (P 1), Neg . Dia ags $ PrpF (P 1)]
    prop "Validates modal tautology on S4: Box p implies Dia p for all groups" $ do
      \tm (Arb ags) ->
        (tm :: TopoEModel) |= Impl (Box ags $ PrpF (P 1)) (Dia ags $ PrpF (P 1))
    prop "Does not satisfy modal contradiction Box p and Dia not p for any agent" $ do
      \ptm (Arb ags) ->
        not ((ptm :: PtTopoEModel) |= Conj [Box ags $ PrpF (P 1), Dia ags . Neg $ PrpF (P 1)])
    prop "Does not satisfy contradiction Box Bot for any agent" $ do
      \ptm (Arb ags) ->
        not ((ptm :: PtTopoEModel) |= Box ags Bot)

  describe "Group Knowledge axioms are satisfied on explicit Topo-e-model" $ do
    prop "New Axiom" $ do
      \f g (GGG (Arb group) (Arb subgroup) (Arb subsubgroup)) tm ->
        (tm :: TopoEModel) |= B subgroup (Impl
          (Conj [f :: Form, B group (g :: Form)])
          (K group (Disj [g, Neg $ K subsubgroup (Neg f)])))
    prop "Evidence monotonicity for all groups" $ do
      \f (GG (Arb group) (Arb subgroup)) tm ->
        (tm :: TopoEModel) |= Impl (Box subgroup (f :: Form)) (Box group f) &&
        tm |= Impl (Forall subgroup f) (Forall group f)
    prop "Inclusion" $ do
      \f tm (Arb ags) ->
        (tm :: TopoEModel) |= Impl (Forall ags (f :: Form)) (Box ags f)
    prop "Group Knowledge of Subgroup Beliefs (KPB,KNB)" $ do
      \f (GG (Arb group) (Arb subgroup)) tm ->
        (tm :: TopoEModel) |= Impl (B subgroup (f :: Form)) (K group $ B subgroup f) &&
        tm |= Impl (Neg $ B subgroup f) (K group (Neg $ B subgroup f))
    prop "Consistency of Group Belief with Distributed Knowledge (BDK)" $ do
      \(GF l) tm ->
        (tm :: TopoEModel) |= Impl
          (Conj [uncurry K t | t <- l])
          (Neg $ B (S.unions [fst t | t <- l]) (Neg $ Conj [snd t | t <- l]))
    prop "Subgroup Knowledge and Group Belief Imply Group Knowledge (KBK)" $ do
      \f (GG (Arb group) (Arb subgroup)) tm ->
        (tm :: TopoEModel) |= Impl (Conj [K subgroup f, B group f]) (K group f)

  describe "S4 Kripke Model and TopoEModel correspondence" $ do
    prop "Kripke Model is translated into valid explicit Topo-e-model" $ do
      \km ->
        isTopoEvidenceModel (expKripkeToExpTopo (km :: S4KripkeModel))
    prop "Translation from Topo results in S4 Kripke model for each agent" $ do
      \tm (Arb ags) ->
        makeReflexive (groupRel ags (expTopoToExpKripke tm) :: Relation) ==
          groupRel ags (expTopoToExpKripke tm) &&
        makeTransitive (groupRel ags (expTopoToExpKripke tm) :: Relation) ==
          groupRel ags (expTopoToExpKripke tm)

  describe "S4 Kripke Model and TopoEModel correspondence" $ do
    prop "Topo -> Kripke -> Topo transl gives same topologies" $ do
      \tm (Arb ags) -> generateTop ags (tm :: TopoEModel) `shouldBe`
        generateTop ags (expKripkeToExpTopo (expTopoToExpKripke tm))

    prop "Not pointed: Kripke -> Topo -> Kripke transl gives same model" $ do
      \km ->
        (km :: S4KripkeModel) `shouldBe` expTopoToExpKripke (expKripkeToExpTopo km)
    prop "Pointed: Kripke -> Topo -> Kripke transl gives same model" $ do
      \pkm ->
        (pkm :: PtS4KripkeModel) `shouldBe` expTopoToExpKripkePt (expKripkeToExpTopoPt pkm)

    prop "Pointed Kripke Models and their corresp. TopoEModels satisfy the same formulas" $ do
       \pkm f ->
        (pkm :: PtS4KripkeModel) |= (f :: Form) `shouldBe` expKripkeToExpTopoPt pkm |= f
    prop "Pointed TopoEModels and their corresp. Kripke Models satisfy the same formulas" $ do
       \ptm f ->
        (ptm :: PtTopoEModel) |= (f :: Form) `shouldBe` expTopoToExpKripkePt ptm |= f