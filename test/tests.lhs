
\section{Tests}\label{sec:tests}

\begin{code}
module Main where

import Topology
import TopoModels
import Syntax
import Semantics
import TestHelpers

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck 

import Data.Set (Set, isSubsetOf)
import qualified Data.Set as S
\end{code}

\begin{code}
{-
  prop "property of one thing" $
    \ x -> (x:: Int) * 2 * 2 === x * 4
  prop "poperty of two things" $
    \ x y -> (x :: Int) * y === y * x
  prop "property of two things with constraints" $
    \ x y -> even (x :: Int) && odd y ==> even (x * y)
  prop "property of two things with dependency" $
    \ x y -> (y :: Int) < x ==> y -10 < x
  
  describe "pForm" $ do
    prop "pForm (P k) should contain k" $
      \k -> pForm (P k) `shouldContain` show k
  describe "prove" $ do
    it "prove the law of excluded middle" $
      prove (Neg (Con (P 1) (Neg (P 1))))
    it "do not prove p1 ^ p2" $
      not $ prove (Con (P 1) (P 2))

-- use a different function to run checks and then return 
-- K axiom
-- formulas that are not valid but satisfiable 
-- write tests that are expected to fail
-}
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
    prop "Preserves the whole space" $ 
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
  {-
  describe "TopoModel semantics" $ do
    prop "Validates the K axiom" $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Validates tautology p or not p" $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Validates tautology p implies p" $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Validates modal tautology p implies p" $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Cannot satisfy contradiction p and not p" $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Cannot satisfy contradiction ............." $ do
      \ts -> (ts :: TopoModel Int) ||= K
    prop "Cannot satisfy modal contradiction ............." $ do
      \ts -> (ts :: TopoModel Int) ||= K
-}

\end{code}


To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.
