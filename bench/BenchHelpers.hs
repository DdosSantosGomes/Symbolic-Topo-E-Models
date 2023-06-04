{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchHelpers where

import KripkeModels (
    PointedS4KripkeModel (..),
    S4KripkeFrame (..),
    S4KripkeModel (..),
 )
import Models (Valuation, randomVal)
import SetTheory (
    Relation,
    isOfSize,
    isOfSizeBetween,
    makeTransitive,
    setElements,
    setOf1,
    subsetSizeOf,
 )
import Syntax (Form (..))
import TopoModels (PointedTopoModel (..), TopoModel (..))
import Topology (TopoSpace (..), fixTopoSpace)

import Data.Set (Set, cartesianProduct, union)
import Data.Set qualified as S

import Test.QuickCheck (
    Arbitrary (arbitrary),
    Gen,
    elements,
    oneof,
    suchThat,
 )
import Text.Printf (printf)

printAndAppendToFile :: String -> String -> IO ()
printAndAppendToFile fileName someString = do
    printf someString
    appendFile fileName someString

nRandomForm :: Int -> Gen Form
nRandomForm 0 = P <$> elements [1 .. 10] -- Fixed vocabulary
nRandomForm n =
    oneof
        [ P <$> elements [1 .. 10]
        , Dis
            <$> nRandomForm (n `div` 2)
            <*> nRandomForm (n `div` 2)
        , Con
            <$> nRandomForm (n `div` 2)
            <*> nRandomForm (n `div` 2)
        , Imp
            <$> nRandomForm (n `div` 2)
            <*> nRandomForm (n `div` 2)
        , Neg <$> nRandomForm (n `div` 2)
        , Dia <$> nRandomForm (n `div` 2)
        , Box <$> nRandomForm (n `div` 2)
        ]

formSize :: Form -> Int
formSize Top = 1
formSize Bot = 1
formSize (P _) = 1
formSize (f `Dis` g) = 1 + formSize f + formSize g
formSize (f `Con` g) = 1 + formSize f + formSize g
formSize (f `Imp` g) = 1 + formSize f + formSize g
formSize (Neg f) = 1 + formSize f
formSize (Dia f) = 1 + formSize f
formSize (Box f) = 1 + formSize f

randNTopoSpace :: (Arbitrary a, Ord a) => Int -> Int -> Gen (TopoSpace a)
randNTopoSpace n _ = do
    (carrier :: Set a) <- arbitrary `suchThat` (`isOfSize` n)
    -- Put an artificial bound on the size of the set, otherwise it takes too long to "fix" the topology
    -- subbasis <- let basis = subsetSizeOf carrier m in setSizeOf basis m
    subbasis <-
        let basis = setOf1 (setElements carrier) `suchThat` (\set -> isOfSizeBetween set 0 5)
         in setOf1 basis `suchThat` (\set -> isOfSizeBetween set 0 5)
    let someTopoSpace = TopoSpace carrier subbasis
    return (fixTopoSpace someTopoSpace)

randNTopoModel :: (Arbitrary a, Ord a) => Int -> Int -> Gen (TopoModel a)
randNTopoModel n m = do
    (TopoSpace space topo) <- randNTopoSpace n m
    -- Random Valuation depending on the points of the space
    -- Fix the number of propositional variables
    val <- randomVal space [1 .. 10]
    return (TopoModel (TopoSpace space topo) val)

randNPointedTopoModel :: (Arbitrary a, Ord a) => Int -> Int -> Gen (PointedTopoModel a)
randNPointedTopoModel n m = do
    (randomModel :: TopoModel a) <- randNTopoModel n m
    let (TopoModel topospace _) = randomModel
    let (TopoSpace carrier _) = topospace
    point <- setElements carrier
    return (PointedTopoModel randomModel point)

randNS4KripkeFrame :: (Arbitrary a, Ord a) => Int -> Int -> Gen (S4KripkeFrame a)
randNS4KripkeFrame n m = do
    (carrier :: Set a) <- arbitrary `suchThat` (`isOfSize` n)
    let carrierSquared = cartesianProduct carrier carrier
    (randomRelation :: Relation a) <- subsetSizeOf carrierSquared m
    let diagonal = S.filter (uncurry (==)) carrierSquared
    let reflexiveRelation = randomRelation `union` diagonal
    let s4Relation = makeTransitive reflexiveRelation
    return (S4KF carrier s4Relation)

randNS4KripkeModel :: (Arbitrary a, Ord a) => Int -> Int -> Gen (S4KripkeModel a)
randNS4KripkeModel n m = do
    (randomFrame :: S4KripkeFrame a) <- randNS4KripkeFrame n m
    let (S4KF carrier _) = randomFrame
    (randomValuation :: Valuation a) <- randomVal carrier [1 .. 10]
    return (S4KM randomFrame randomValuation)

randNPointedS4KripkeModel :: (Arbitrary a, Ord a) => Int -> Int -> Gen (PointedS4KripkeModel a)
randNPointedS4KripkeModel n m = do
    (randomModel :: S4KripkeModel a) <- randNS4KripkeModel n m
    let (S4KM frame _) = randomModel
    let (S4KF carrier _) = frame
    point <- setElements carrier
    return (PS4KM randomModel point)