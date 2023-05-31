\section{KripkeModels}\label{sec:KripkeModels}

\begin{code}

module KripkeModels where

import Data.Set (Set, cartesianProduct, union)
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary (arbitrary), suchThat)

import Models (Valuation, randomVal)
import SetTheory (Relation, isOfSizeBetween, makeTransitive, setElements, subsetOf)

\end{code}

\begin{code}

data S4KripkeFrame a
    = S4KF
        (Set a) -- Carrier set
        (Relation a) -- Relation
    deriving (Eq, Show)

data S4KripkeModel a = S4KM (S4KripkeFrame a) (Valuation a)
    deriving (Eq, Show)

data PointedS4KripkeModel a = PS4KM (S4KripkeModel a) a
    deriving (Eq, Show)

\end{code}

% TODO - Write about arbitrary Kripke frames

\begin{code}

instance (Arbitrary a, Ord a) => Arbitrary (S4KripkeFrame a) where
    arbitrary = do
        (carrier :: Set a) <- arbitrary `suchThat` (\set -> isOfSizeBetween set 1 10)
        let carrierSquared = cartesianProduct carrier carrier
        (randomRelation :: Relation a) <- subsetOf carrierSquared
        let diagonal = S.filter (uncurry (==)) carrierSquared
        let reflexiveRelation = randomRelation `union` diagonal
        let s4Relation = makeTransitive reflexiveRelation
        return (S4KF carrier s4Relation)

instance (Arbitrary a, Ord a) => Arbitrary (S4KripkeModel a) where
    arbitrary = do
        (randomFrame :: S4KripkeFrame a) <- arbitrary
        let (S4KF carrier _) = randomFrame
        (randomValuation :: Valuation a) <- randomVal carrier [1 .. 10]
        return (S4KM randomFrame randomValuation)

instance (Arbitrary a, Ord a) => Arbitrary (PointedS4KripkeModel a) where
    arbitrary = do
        (randomModel :: S4KripkeModel a) <- arbitrary
        let (S4KM frame _) = randomModel
        let (S4KF carrier _) = frame
        point <- setElements carrier
        return (PS4KM randomModel point)

\end{code}