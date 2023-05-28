
\section{Tests}\label{sec:tests}

\begin{code}
module Main where

import Topology
import TopoModels
import Syntax
import Semantics

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
\end{code}


To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.
