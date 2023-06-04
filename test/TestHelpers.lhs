\section{Test Preliminaries}\label{sec:TestHelpers}

\begin{code}

{-# LANGUAGE ScopedTypeVariables #-}

module TestHelpers where

import Data.Set
import Data.Set qualified as S
import Test.QuickCheck (Arbitrary (arbitrary))
import TopoModels ( PointedTopoModel, TopoModel )
import KripkeModels ( PointedS4KripkeModel, S4KripkeModel )
import ModelConversion ( toPointedTopoModel, toTopoModel )

import SetTheory (closeUnderIntersection, closeUnderUnion, subsetOf)
import Syntax ( Form(Imp, Box, Dia, P) )
import Topology ( fixTopoSpace, TopoSpace(..) )

\end{code}

Artificial new types to give a subset of the space and a topology only used for tests. 
This allows efficient generation of subsets, instead of randomly guessing of subsets as a constraint which
may take a really long time when testing and may make `QuickCheck` give up.

\begin{code}
data SubsetTopoSpace a = STS (Set a) (TopoSpace a)
    deriving (Eq, Show)

instance (Arbitrary a, Ord a) => Arbitrary (SubsetTopoSpace a) where
  arbitrary = do
    ((TopoSpace space topo)::TopoSpace a) <- arbitrary
    subset <- subsetOf space
    return (STS subset (TopoSpace space topo))

data SSubsetTopoSpace a = SSTS (Set a) (Set a) (TopoSpace a)
    deriving (Eq, Show)

instance (Arbitrary a, Ord a) => Arbitrary (SSubsetTopoSpace a) where
  arbitrary = do
    ((TopoSpace space topo)::TopoSpace a) <- arbitrary
    subset <- subsetOf space
    anotherSubset <- subsetOf space
    return (SSTS subset anotherSubset (TopoSpace space topo))

data S4KripkeModelTopoModel a = S4KMTM (S4KripkeModel a) (TopoModel a)
    deriving (Eq, Show)

instance (Arbitrary a, Ord a) => Arbitrary (S4KripkeModelTopoModel a) where
  arbitrary = do
    (s4km::S4KripkeModel a) <- arbitrary
    let (tm :: TopoModel a) = toTopoModel s4km
    return (S4KMTM s4km tm)

data PointedS4KripkeModelTopoModel a = PS4KMTM (PointedS4KripkeModel a) (PointedTopoModel a)
    deriving (Eq, Show)

instance (Arbitrary a, Ord a) => Arbitrary (PointedS4KripkeModelTopoModel a) where
  arbitrary = do
    (s4km::PointedS4KripkeModel a) <- arbitrary
    let (tm :: PointedTopoModel a) = toPointedTopoModel s4km
    return (PS4KMTM s4km tm)
\end{code}

Example variables from \texttt{Topology} module used for actually running the examples in the test suite.

\begin{code}
s0 :: Set Int
s0 = S.fromList [1] 
s1 :: Set Int
s1 = S.fromList [2] 
s2 :: Set Int
s2 = S.fromList [3, 4] 
s3 :: Set Int
s3 = S.fromList [1, 2, 3] 
s4 :: Set Int
s4 = S.fromList [2, 3]
s5 :: Set Int
s5 = S.fromList [3, 4]
s6 :: Set Int
s6 = S.fromList [1, 2]
s7 :: Set Int
s7 = S.fromList [1, 3]

topology :: Set (Set Int)
topology = (closeUnderUnion . closeUnderIntersection) $ S.fromList [s5, s6, s7]

badTS :: TopoSpace Integer
badTS = TopoSpace (S.fromList [1,2,3]) (S.fromList [S.fromList [1,2], S.fromList[2,3]])

goodTS :: TopoSpace Integer
goodTS = fixTopoSpace badTS

topoSpace :: TopoSpace Int
topoSpace = TopoSpace (S.fromList [1, 2, 3, 4]) topology

\end{code}

Modal logic axioms that our models are supposed to validate.

\begin{code}

kAxiom :: Form
kAxiom = Box (P 1 `Imp` P 2) `Imp` (Box (P 1) `Imp` Box (P 2))

tAxiom :: Form
tAxiom = P 1 `Imp` Dia (P 1)

fourAxiom :: Form
fourAxiom = Dia (Dia (P 1)) `Imp` Dia (P 1)
\end{code}