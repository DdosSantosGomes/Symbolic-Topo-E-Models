\section{KripkeModels}\label{sec:KripkeModels}

\begin{code}

module KripkeModels where

import Data.Set (Set)
import Test.QuickCheck ( Arbitrary(arbitrary))

import Models (Valuation)

\end{code}

\begin{code}

data S4KripkeFrame a
    = S4KF
        (Set a) -- Carrier set
        (Set (a, a)) -- Relation
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
        
        {-
            TODO -
            1. Gen random carrier set
            2. Get cross-product of carrier
            3. Gen random subset of cross-product (this will not be S4)
            4. Fix relation to be S4 (make refl. and tran.)
            5. Construct and return S4KripkeFrame using carrier and fixed relation
        -}
        return undefined

instance (Arbitrary a, Ord a) => Arbitrary (PointedS4KripkeModel a) where
    arbitrary = do
        {-
            TODO -
            1. Gen random S4KripkeFrame
            2. Gen random valuation
            3. Construct and return PointedS4KripkeModel
        -}
        return undefined

\end{code}