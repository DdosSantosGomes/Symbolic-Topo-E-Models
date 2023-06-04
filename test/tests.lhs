\section{Testing}\label{sec:tests}

\begin{code}
module Main where

import KripkeModels ( PointedS4KripkeModel, S4KripkeModel )
import SetTheory 
import Topology 
import TopoModels (TopoModel, PointedTopoModel)
import Syntax
import Semantics ( Semantics((|=)) )
import TestHelpers


import Test.Hspec
    ( hspec, describe, it, shouldBe, shouldThrow, anyException )
import Test.Hspec.QuickCheck ( prop)
import Test.QuickCheck () 
import Control.Exception (evaluate)

import Data.Set (Set, isSubsetOf)
import qualified Data.Set as S
\end{code}

\begin{code}
main :: IO ()
main = hspec $ do
  describe "TopoSpace generation" $ do
    prop "Arbitrary TopoSpace satisfies the open set definition of a topo space" $ do
      \ts -> isTopoSpace (ts :: TopoSpace Int)
    prop "The subset in arbitrary SubsetTopoSpace is indeed a subset of the space" $ do
      \(STS setA (TopoSpace space _)) -> (setA :: Set Int) `isSubsetOf` space
    prop "The two subsets in arbitrary SSubsetTopoSpace are indeed subsets of the space" $ do
      \(SSTS setA setB (TopoSpace space _)) -> (setA :: Set Int) `isSubsetOf` space && (setB :: Set Int) `isSubsetOf` space
  describe "Kuratowski Axioms for the closure operator" $ do
    prop "Preserves the empty set" $ do
        \x -> closure S.empty (x :: TopoSpace Int) `shouldBe` S.empty
    prop "Is extensive for all A \\subseteq X" $ do
        \ (STS setA ts) -> (setA :: Set Int) `isSubsetOf` closure setA ts
    prop "Is idempotent for all A \\subseteq X" $ do
        \(STS setA ts) -> closure (setA :: Set Int) ts `shouldBe` closure (closure setA ts) ts
    prop "Distributes over binary unions" $ do
        \(SSTS setA setB ts) -> 
          closure ((setA :: Set Int) `S.union` setB) ts `shouldBe` 
          closure setA ts `S.union` closure setB ts
  describe "Kuratowski Axioms for the interior operator" $ do
    prop "Preserves the whole space" $ do
        \(TopoSpace space topo) -> interior (space :: Set Int) (TopoSpace space topo) `shouldBe` space
    prop "Is intensive for all A \\subseteq X" $ do
        \ (STS setA ts) -> interior (setA :: Set Int) ts `isSubsetOf` setA
    prop "Is idempotent for all A \\subseteq X" $ do
         \(STS setA ts) -> interior (setA :: Set Int) ts `shouldBe` interior (interior setA ts) ts
    prop "Distributes over binary intersections" $ do
        \(SSTS setA setB ts) -> 
          interior ((setA :: Set Int) `S.intersection` setB) ts `shouldBe` 
          interior setA ts `S.intersection` interior setB ts
  describe "Examples from the Topology module" $ do
    it "closeUnderUnion $ Set.fromList [s0, s1, s2]" $ do
      let result = S.fromList [S.fromList [1], S.fromList [1,2], S.fromList [1,2,3,4], S.fromList [1,3,4],S.fromList [2],S.fromList [2,3,4],S.fromList [3,4]]
      closeUnderUnion (S.fromList [s0, s1, s2]) `shouldBe` result
    it "closeUnderIntersection $ Set.fromList [s0, s1, s2]" $ do
      let result = S.fromList [S.fromList [], S.fromList [1], S.fromList [2], S.fromList [3,4]]
      closeUnderIntersection (S.fromList [s0, s1, s2]) `shouldBe` result
    it "closeUnderUnion $ Set.fromList [s3, s4, s5]" $ do
      let result = S.fromList [S.fromList [1,2,3], S.fromList [1,2,3,4], S.fromList [2,3], S.fromList [2,3,4], S.fromList [3,4]]
      closeUnderUnion (S.fromList [s3, s4, s5]) `shouldBe` result
    it "closeUnderIntersection $ Set.fromList [s3, s4, s5]" $ do
      let result = S.fromList [S.fromList [1,2,3], S.fromList [2,3], S.fromList [3], S.fromList [3,4]]
      closeUnderIntersection (S.fromList [s3, s4, s5]) `shouldBe` result
    it "(closeUnderUnion . closeUnderIntersection) $ Set.fromList [s5, s6, s7]" $ do
      let result = S.fromList [S.fromList [], S.fromList [1], S.fromList [1,2], S.fromList [1,2,3], S.fromList [1,2,3,4], S.fromList [1,3], S.fromList [1,3,4], S.fromList [3], S.fromList [3,4]]
      (closeUnderUnion . closeUnderIntersection) (S.fromList [s5, s6, s7]) `shouldBe` result
    it "isTopoSpace (TopoSpace (arbUnion Set.fromList [s5, s6, s7]) topology)" $ do
      isTopoSpace (TopoSpace (arbUnion $ S.fromList [s5, s6, s7]) topology)
    it "isTopoSpace badTS" $ do
      not . isTopoSpace $ badTS
    it "isTopoSpace goodTS" $ do
      isTopoSpace goodTS
    it "isTopoSpace (fixTopoSpace goodTS)" $ do
      isTopoSpace (fixTopoSpace goodTS)
    it "closeds topoSpace" $ do
      let result = S.fromList [S.fromList [], S.fromList [1,2], S.fromList [1,2,3,4], S.fromList [1,2,4], S.fromList [2], S.fromList [2,3,4], S.fromList [2,4], S.fromList [3,4], S.fromList [4]]
      closeds topoSpace `shouldBe` result
    it "openNbds 2 topoSpace" $ do
      let result = S.fromList [S.fromList [1,2], S.fromList [1,2,3], S.fromList [1,2,3,4]]
      openNbds 2 topoSpace `shouldBe` result
    it "(S.fromList [1]) `isOpenIn` topoSpace" $ do
      S.fromList [1] `isOpenIn` topoSpace
    it "(S.fromList [1]) `isClosedIn` topoSpace" $ do
      not (S.fromList [1] `isClosedIn` topoSpace)
    it "(S.fromList []) `isClopenIn` topoSpace" $ do
      S.fromList [] `isClopenIn` topoSpace
    it "interior (Set.fromList [1]) topoSpace" $ do
      let result = S.fromList [1]
      interior (S.fromList [1]) topoSpace `shouldBe` result
    it "closure (Set.fromList [1]) topoSpace" $ do
      let result = S.fromList [1,2]
      closure (S.fromList [1]) topoSpace `shouldBe` result
    it "fixTopoSpace (TopoSpace (S.fromList [1,2,3]) topology)" $ do
       evaluate (fixTopoSpace (TopoSpace (S.fromList [1,2,3]) topology)) `shouldThrow` anyException
  describe "TopoModel semantics" $ do
    prop "Validates the K axiom" $ do
      \ts -> (ts :: TopoModel Int) |= kAxiom
    prop "Validates tautology: p or not p" $ do
      \ts -> (ts :: TopoModel Int) |= (P 1 `Dis` Neg (P 1))
    prop "Validates tautology: p implies p" $ do
      \ts -> (ts :: TopoModel Int) |= (P 1 `Imp` P 1)
    prop "Validates tautology: p implies (q implies (p and q))" $ do
      \ts -> (ts :: TopoModel Int) |= (P 1 `Imp` (P 2 `Imp` (P 1 `Con` P 2)))
    prop "Validates modal tautology: Dia p or not Dia p"$ do
      \ts -> (ts :: TopoModel Int) |= (Dia (P 1)`Dis` Neg (Dia (P 1)))
    prop "Validates modal tautology: Box p implies Dia p"$ do
      \ts -> (ts :: TopoModel Int) |= (Box (P 1) `Imp` Dia (P 1))
    prop "Cannot satisfy contradiction p and not p" $ do
      \ts -> not ((ts :: PointedTopoModel Int) |= (P 1 `Con` Neg (P 1)))
    prop "Cannot satisfy contradiction ((P or Q) implies R) and not ((P or Q) implies R)" $ do
      \ts -> not ((ts :: PointedTopoModel Int) |= (((P 1 `Dis` P 2) `Imp` P 3) `Con` Neg ((P 1 `Dis` P 2) `Imp` P 3)))
    prop "Cannot satisfy modal contradiction: Dia p or not Dia p" $ do
      \ts -> not ((ts :: PointedTopoModel Int) |= (Dia (P 1) `Con` Neg (Dia (P 1))))
    prop "Cannot satisfy modal contradiction: Box p and Dia not p" $ do
      \ts -> not ((ts :: PointedTopoModel Int) |= (Box (P 1) `Con` Dia (Neg (P 1))))
  describe "S4 Kripke Model and TopoModel correspondence" $ do
    prop "Both validate the K axiom (distribution of box)" $ do
      \(S4KMTM km tm) -> (km :: S4KripkeModel Int) |= kAxiom && tm |= kAxiom
    prop "Both validate the T axiom (reflexivity)" $ do
      \(S4KMTM km tm) -> (km :: S4KripkeModel Int) |= tAxiom && tm |= tAxiom
    prop "Both validate the 4 axiom (transitivity)" $ do
      \(S4KMTM km tm) -> (km :: S4KripkeModel Int) |= fourAxiom && tm |= fourAxiom
    prop "Corresponding KMs and TMs satisfy the same formulas" $ do
       \(PS4KMTM km tm, f) -> (km :: PointedS4KripkeModel Int) |= (f :: Form) == tm |= f

\end{code}
