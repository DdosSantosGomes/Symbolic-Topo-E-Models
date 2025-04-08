module Syntax where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized
  , elements
  , oneof
  , listOf
  )
import Data.List (nub)
import SMCDEL.Language (Prp (..), Agent)
import SMCDEL.Internal.Help (lfp)
import Data.Set (Set)
import SetTheory (subsetOf1)
import qualified Data.Set as S


{-
  Language, default vocabulary and agents, and generation of arbitrary formulas.
-}


-- Default vocabulary.
defaultVocab :: [Prp]
defaultVocab = [P 0, P 1, P 2]

type Group = Set Agent

-- Default group of agents.
defaultAgents:: Group
defaultAgents = S.fromList $ map show [(1::Integer)..5]

newtype ArbGroup = Arb Group deriving (Eq,Ord,Show)

-- Arbitrary subgroup of default agents.
instance Arbitrary ArbGroup where
  arbitrary = do
    subgroup <- subsetOf1 defaultAgents
    return (Arb subgroup)

-- Syntax of evidence model language (including some abbreviations).
data Form
  = Top
  | Bot
  | PrpF Prp
  | Neg Form
  | Conj [Form]
  | Disj [Form]
  | Impl Form Form
  | Box Group Form
  | Dia Group Form
  | Forall Group Form
  | K Group Form
  | B Group Form
  deriving (Eq, Show, Ord)

-- Simplify a formula to an equivalent formula.
simplify :: Form -> Form
simplify = lfp simStep

simStep :: Form -> Form
simStep Top             = Top
simStep Bot             = Bot
simStep (PrpF p)        = PrpF p
simStep (Neg Top)       = Bot
simStep (Neg Bot)       = Top
simStep (Neg (Neg f))   = simStep f
simStep (Neg f)         = Neg $ simStep f
simStep (Conj [])       = Top
simStep (Conj [f])      = simStep f
simStep (Conj fs)      | Bot `elem` fs = Bot
                       | or [ Neg f `elem` fs | f <- fs ] = Bot
                       | otherwise = Conj (nub $ concatMap unpack fs) where
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
simStep (Disj [])       = Bot
simStep (Disj [f])      = simStep f
simStep (Disj fs)      | Top `elem` fs = Top
                       | or [ Neg f `elem` fs | f <- fs ] = Top
                       | otherwise = Disj (nub $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Impl Bot _)    = Top
simStep (Impl _ Top)    = Top
simStep (Impl Top f)    = simStep f
simStep (Impl f Bot)    = Neg (simStep f)
simStep (Impl f g)     | f==g      = Top
                       | otherwise = Impl (simStep f) (simStep g)
simStep (Box _ Top)     = Top
simStep (Box _ Bot)     = Bot
simStep (Box ags f)     = Box ags (simStep f)
simStep (Dia ags f)     = Dia ags (simStep f)
simStep (Forall _ Top)  = Top
simStep (Forall _ Bot)  = Bot
simStep (Forall ags f)  = Forall ags (simStep f)
simStep (K _ Bot)       = Bot
simStep (K _ Top)       = Top
simStep (K ags f)       = K ags (simStep f)
simStep (B _ Top)       = Top
simStep (B _ Bot)       = Bot
simStep (B ags f)       = B ags (simStep f)

{-
  Generate arbitrary sized formulas.
  Adapted from SMCDEL.Language.
-}
instance Arbitrary Form where
    arbitrary = sized randomForm
      where
        randomForm :: Int -> Gen Form
        randomForm 0 = oneof [ pure Top
                             , pure Bot
                             , PrpF <$> elements defaultVocab
                             ]
        randomForm n = oneof [ pure Top
                             , pure Bot
                             , PrpF <$> elements defaultVocab
                             , Neg <$> st
                             , Conj <$> listOf st
                             , Disj <$> listOf st
                             , Impl <$> st <*> st
                             , Box <$> subsetOf1 defaultAgents <*> st
                             , Dia <$> subsetOf1 defaultAgents <*> st
                             , Forall <$> subsetOf1 defaultAgents <*> st
                             , K <$> subsetOf1 defaultAgents <*> st
                             , B <$> subsetOf1 defaultAgents <*> st
                             ]
          where
            st = randomForm (n `div` 3)


-- Boolean formulas (adapted from SMCDEL.Language to work with our Form type).


newtype BF = BF Form deriving (Eq,Ord,Show)

-- Generate arbitrary sized boolean formulas.
randomBFWith :: [Prp] -> Int -> Gen BF
randomBFWith allprops sz = BF <$> bf' sz where
  bf' 0 = PrpF <$> elements allprops
  bf' n = oneof [ pure Top
                , pure Bot
                , PrpF <$> elements allprops
                , Neg <$> st
                , (\x y -> Conj [x,y]) <$> st <*> st
                , (\x y z -> Conj [x,y,z]) <$> st <*> st <*> st
                , (\x y -> Disj [x,y]) <$> st <*> st
                , (\x y z -> Disj [x,y,z]) <$> st <*> st <*> st
                , Impl <$> st <*> st
                ]
    where
      st = bf' (n `div` 3)

instance Arbitrary BF where
  arbitrary = sized $ randomBFWith defaultVocab