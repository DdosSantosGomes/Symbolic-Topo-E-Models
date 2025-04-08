{-# LANGUAGE ImportQualifiedPost #-}

module SetTheory where

import SMCDEL.Internal.Help (lfp)
import Data.Set
  ( Set
  , elemAt
  , intersection
  , union
  )
import Data.Set qualified as S
import Test.QuickCheck
  ( Arbitrary
  , Gen
  , elements
  , listOf
  , oneof
  , sublistOf
  , vectorOf
  , listOf
  , listOf1
  )
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Test.QuickCheck.Gen (suchThat)


{-
  Helper functions with respect to set theory and relations.

  Note: arbitrary and finite unions/intersections coincide on finite models,
  so we compute union (arbitrary) and intersection (finite) in the same way;
  we only need to manually add the empty set in the arbitrary union.
-}


type World = Int
type Relation = M.Map World (Set World)


{-
  Close a given set of sets under arbitrary unions. Recursively add binary unions
  until a fixpoint is reached and add the empty set (which is the empty union).
-}
closeUnderUnion :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderUnion =
  S.insert S.empty . lfp (\set -> set `union` newsets set) where
  newsets set = S.fromList [ s1 `union` s2 | let listOfSets = S.toList set
                                           , s1 <- listOfSets
                                           , s2 <- listOfSets
                           ]

{-
  Close a given set of sets under arbitrary intersections. Recursively add binary
  intersections until a fixpoint is reached.
-}
closeUnderIntersection :: (Ord a) => Set (Set a) -> Set (Set a)
closeUnderIntersection = lfp (\set -> set `union` newsets set) where
  newsets set = S.fromList [ s1 `intersection` s2 | let listOfSets = S.toList set
                                                  , s1 <- listOfSets
                                                  , s2 <- listOfSets
                           ]

-- Return the arbitrary intersection of a set of sets.
arbIntersection :: (Eq a, Ord a) => Set (Set a) -> Set a
arbIntersection sets
  | sets == S.empty = error "Cannot take the intersection of the empty set."
  | otherwise = foldr intersection (elemAt 0 sets) sets

{-
  Make a given relation reflexive. Given a world w (the key), add w to its own
  image (val).
-}
makeReflexive :: Relation -> Relation
makeReflexive = M.mapWithKey S.insert

{-
  Recursively make a given relation transitive. For each world, given its current
  image, add all worlds reachable from any world in its image to the current image
  until a fixpoint is reached.
-}
makeTransitive :: Relation -> Relation
makeTransitive rel = lfp makeTransOnce rel where
  makeTransOnce = M.map addRel
  addRel val = S.unions [rel ! w | w <- S.toList val] `S.union` val


-- Arbitrary Set Generation, based on existing functions for arbitrary list generation.


setOneOf :: Set (Gen a) -> Gen a
setOneOf = oneof . S.toList

subsetOf :: (Arbitrary a, Ord a) => Set a -> Gen (Set a)
subsetOf = fmap S.fromList . sublistOf . S.toList

subsetOf1 :: (Arbitrary a, Ord a) => Set a -> Gen (Set a)
subsetOf1 xs = do
  getList <- sublistOf (S.toList xs) `suchThat` (not . null)
  return (S.fromList getList)

setOf :: (Arbitrary a, Ord a) => Gen a -> Gen (Set a)
setOf = fmap S.fromList . listOf

setOf1 :: (Arbitrary a, Ord a) => Gen a -> Gen (Set a)
setOf1 = fmap S.fromList . listOf1

setElements :: Set a -> Gen a
setElements = elements . S.toList

isOfSize :: Set a -> Int -> Bool
isOfSize set k = S.size set == k

isOfSizeBetween :: Int -> Int -> Set a -> Bool
isOfSizeBetween lower upper set = lower <= S.size set && S.size set <= upper

setSizeOf :: (Ord a) => Gen a -> Int -> Gen (Set a)
setSizeOf g k = fmap S.fromList (vectorOf k g)

subsetSizeOf :: (Ord a) => Set a -> Int -> Gen (Set a)
subsetSizeOf set k = fmap S.fromList (vectorOf k (setElements set))