{-# LANGUAGE BlockArguments #-}

module Main where

import Test.Hspec
import ExplicitSpec
import SymbolicSpec

main :: IO ()
main = hspec $ do
  describe "Explicit implementation" ExplicitSpec.spec
  describe "Symbolic implementation" SymbolicSpec.spec

