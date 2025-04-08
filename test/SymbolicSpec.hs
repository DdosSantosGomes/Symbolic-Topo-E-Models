{-# LANGUAGE BlockArguments #-}

module SymbolicSpec where
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.Hspec.QuickCheck (prop, modifyMaxDiscardRatio, modifyMaxSuccess)
import Test.QuickCheck (counterexample, discardAfter)
import qualified Data.Set as S
import SMCDEL.Language (Prp (..))

import Explicit.Semantics (Semantics (..))
import TestHelpers
  ( kAxiom
  , tAxiom
  , fourAxiom
  , myStm
  , TwoGroups (GG)
  , ThreeGroups (GGG)
  , GFPair (..)
  )
import Syntax (Form (..), ArbGroup (Arb))
import Symbolic.Semantics
  ( SymTopoEModel
  , PtSymTopoEModel
  , isSymTopoEvidenceModel
  , isSymTopoEvidenceModel'
  )
import ModelConversion
  ( symTopoToExpTopo
  , symTopoToExpTopoPt
  , expTopoToSymTopo
  , expTopoToSymTopoPt
  )
import Explicit.TopoEModels
  ( TopoEModel
  , PtTopoEModel
  , isTopoEvidenceModel
  , isTopoEvidenceModel'
  )


{-
  Testing of the implementation of the symbolic topo-structure.
-}


spec :: Spec
spec = do
  describe "SymTopoEModel generation" $ do
    it "Example stm is ags symbolic topo-e-model" $ do
      isSymTopoEvidenceModel myStm
    prop "Arbitrary SymTopoEModel is ags symbolic topo-e-model" $ do
      \stm -> isSymTopoEvidenceModel (stm :: SymTopoEModel)

  describe "Symbolic semantics" $ do
    prop "Kuratowski axioms satisfied for Interior (= Box)" $ do
      \stm (Arb ags) -> (stm :: SymTopoEModel) |= Conj [
        Box ags Top,
        Impl (Box ags(PrpF $ P 1)) (Box ags $ Box ags (PrpF $ P 1)),
        Impl (Box ags (PrpF $ P 1)) (PrpF $ P 1),
        Impl (Box ags $ Conj [PrpF $ P 1, PrpF $ P 2]) (Conj [Box ags (PrpF $ P 1), Box ags (PrpF $ P 2)]),
        Impl (Conj [Box ags (PrpF $ P 1), Box ags (PrpF $ P 2)]) (Box ags $ Conj [PrpF $ P 1, PrpF $ P 2])
        ]
    prop "Kuratowski axioms satisfied for Closure (= Dia)" $ do
      \stm (Arb ags) -> (stm :: SymTopoEModel) |= Conj [
        Neg (Dia ags Bot),
        Impl (Dia ags $ Dia ags (PrpF $ P 1)) (Dia ags (PrpF $ P 1)),
        Impl (PrpF $ P 1) (Dia ags (PrpF $ P 1)),
        Impl (Dia ags $ Disj [PrpF $ P 1, PrpF $ P 2]) (Disj [Dia ags (PrpF $ P 1), Dia ags (PrpF $ P 2)]),
        Impl (Disj [Dia ags (PrpF $ P 1), Dia ags (PrpF $ P 2)]) (Dia ags $ Disj [PrpF $ P 1, PrpF $ P 2])
        ]
    prop "Validates the K, T, and 4 axioms for all agents" $ do
      \stm (Arb ags) ->
        ((stm :: SymTopoEModel) |= kAxiom ags) &&
        (stm |= tAxiom ags) &&
        (stm |= fourAxiom ags)
    prop "Validates tautology p or not p, does not satisfy p and not p" $ do
      \stm ->
        (stm :: SymTopoEModel) |= Disj [PrpF (P 1), Neg $ PrpF (P 1)] &&
          not (stm |= Conj [PrpF (P 1), Neg $ PrpF (P 1)])
    prop "Validates modal tautology Dia p or not Dia p for all agents" $ do
      \stm (Arb ags) ->
        (stm :: SymTopoEModel) |= Disj [Dia ags $ PrpF (P 1), Neg . Dia ags $ PrpF (P 1)]
    prop "Validates modal tautology on S4: Box p implies Dia p for all agents" $ do
      \stm (Arb ags) ->
        (stm :: SymTopoEModel) |= Impl (Box ags $ PrpF (P 1)) (Dia ags $ PrpF (P 1))
    prop "Does not satisfy modal contradiction Box p and Dia not p for any agent" $ do
      \pstm (Arb ags) ->
        not ((pstm :: PtSymTopoEModel) |= Conj [Box ags $ PrpF (P 1), Dia ags . Neg $ PrpF (P 1)])
    prop "Does not satisfy contradiction Box Bot for any agent" $ do
      \pstm (Arb ags) ->
        not $ (pstm :: PtSymTopoEModel) |= Box ags Bot

  describe "Group Knowledge axioms are satisfied on symbolic Topo-e-model" $ do
    prop "New Axiom" $ do
      \f g (GGG (Arb group) (Arb subgroup) (Arb subsubgroup)) stm ->
        (stm :: SymTopoEModel) |= B subgroup (Impl
          (Conj [f :: Form, B group (g :: Form)])
          (K group (Disj [g, Neg $ K subsubgroup (Neg f)])))
    prop "Evidence monotonicity for all groups" $ do
      \f (GG (Arb group) (Arb subgroup)) stm ->
        (stm :: SymTopoEModel) |= Impl (Box subgroup (f :: Form)) (Box group f) &&
        stm |= Impl (Forall subgroup f) (Forall group f)
    prop "Inclusion" $ do
      \f stm (Arb ags) ->
        (stm :: SymTopoEModel) |= Impl (Forall ags (f :: Form)) (Box ags f)
    prop "Group Knowledge of Subgroup Beliefs (KPB,KNB)" $ do
      \f (GG (Arb group) (Arb subgroup)) stm ->
        (stm :: SymTopoEModel) |= Impl (B subgroup (f :: Form)) (K group $ B subgroup f) &&
        stm |= Impl (Neg $ B subgroup f) (K group (Neg $ B subgroup f))
    prop "Consistency of Group Belief with Distributed Knowledge (BDK)" $ do
      \(GF l) stm ->
        (stm :: SymTopoEModel) |= Impl
          (Conj [uncurry K t | t <- l])
          (Neg $ B (S.unions [fst t | t <- l]) (Neg $ Conj [snd t | t <- l]))
    prop "Subgroup Knowledge and Group Belief Imply Group Knowledge (KBK)" $ do
      \f (GG (Arb group) (Arb subgroup)) stm ->
        (stm :: SymTopoEModel) |= Impl (Conj [K subgroup f, B group f]) (K group f)

  describe "SymTopoEModel <-> TopoEModel translation correctness" $ do
    it "Example Symbolic topo-e-model is translated into valid explicit topo-e-model" $ do
      isTopoEvidenceModel (symTopoToExpTopo myStm)
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Symbolic topo-e-model is translated into valid explicit topo-e-model" $ do
        \stm -> discardAfter 2000 $
          counterexample (show $ symTopoToExpTopo (stm :: SymTopoEModel)) $
          counterexample (show $ isTopoEvidenceModel' (symTopoToExpTopo (stm :: SymTopoEModel))) $
          isTopoEvidenceModel (symTopoToExpTopo (stm :: SymTopoEModel))
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Symbolic topo-e-model and corresp. explicit topo-e-model validate the same formulas" $ do
        \stm f -> discardAfter 2000 $
          counterexample (show $ symTopoToExpTopo (stm :: SymTopoEModel)) $
          (stm :: SymTopoEModel) |= (f :: Form) `shouldBe` symTopoToExpTopo stm |= f
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Pointed symbolic topo-e-model and corresp. explicit model satisfy the same formulas" $ do
        \pstm f -> discardAfter 2000 $
          counterexample (show $ symTopoToExpTopoPt (pstm :: PtSymTopoEModel)) $
          (pstm :: PtSymTopoEModel) |= (f :: Form) `shouldBe` symTopoToExpTopoPt pstm |= f

    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Explicit topo-e-model is translated into valid symbolic topo-e-model" $ do
        \tm -> discardAfter 2000 $
          counterexample (show $ expTopoToSymTopo (tm :: TopoEModel)) $
          counterexample (show $ isSymTopoEvidenceModel' (expTopoToSymTopo (tm :: TopoEModel))) $
          isSymTopoEvidenceModel (expTopoToSymTopo (tm :: TopoEModel))
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Explicit topo-e-model is translated into symtem that doesn't validate Box Bot" $ do
        \tm (Arb ags) -> discardAfter 2000 $
          counterexample (show $ expTopoToSymTopo (tm :: TopoEModel)) $
          not $ expTopoToSymTopo (tm :: TopoEModel) |= Box ags Bot
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Pointed exp. topo-e-model is translated into symtem that doesn't sat. Box Bot" $ do
        \ptm (Arb ags) -> discardAfter 2000 $
          counterexample (show $ expTopoToSymTopoPt (ptm :: PtTopoEModel)) $
          not $ expTopoToSymTopoPt (ptm :: PtTopoEModel) |= Box ags Bot
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Explicit topo-e-model and corresp. symbolic topo-e-model validate the same formulas" $ do
        \tm f -> discardAfter 2000 $
          counterexample (show $ expTopoToSymTopo (tm :: TopoEModel)) $
          (tm :: TopoEModel) |= (f :: Form) `shouldBe` expTopoToSymTopo tm |= f
    modifyMaxSuccess (*10) . modifyMaxDiscardRatio (*100) $
      prop "Pointed explicit topo-e-model and corresp. symbolic model satisfy the same formulas" $ do
        \ptm f -> discardAfter 2000 $
          counterexample (show $ expTopoToSymTopoPt (ptm :: PtTopoEModel)) $
          (ptm :: PtTopoEModel) |= (f :: Form) `shouldBe` expTopoToSymTopoPt ptm |= f