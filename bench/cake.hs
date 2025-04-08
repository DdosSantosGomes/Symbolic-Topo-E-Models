module Main where

import Control.Monad (when)
import Criterion.Main
import qualified Criterion.Types
import Data.List
import qualified Data.ByteString.Lazy as BL
import Data.Char (isSpace)
import Data.Csv
import Data.List.Split
import Data.Maybe
import Data.Scientific
import qualified Data.Vector as V
import Numeric
import System.Directory
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import SMCDEL.Language (Prp (..))
import SMCDEL.Internal.Help (powerset)
import Data.DecisionDiagram.BDD

import Syntax
import Explicit.TopoEModels
import Explicit.Semantics
import ModelConversion
import Symbolic.Semantics
import SetTheory


{-
  Benchmarking. We compare four models with respect to performance:
    (1) Symbolic topo-structure
    (2) Explicit model, translated to symbolic structure
    (3) Explicit model
    (4) Symbolic structure, translated to explicit model.

  We evaluate the specification formula on the exponential variant of the cake
  example.
-}


main :: IO ()
main = prepareMain >> benchMain >> convertMain

benchMain :: IO ()
benchMain = defaultMainWith myConfig (map mybench
       [ ("SymExpo"     , \ n -> cakeParentsSymExpo n                      |= cakeForm n, [4..11] )
       , ("ExpToSymExpo", \ n -> expTopoToSymTopoPt (cakeParentsExpo n)    |= cakeForm n, [4..11] )
       , ("ExpExponential" , \ n -> cakeParentsExpo n                      |= cakeForm n, [4..10] )
       , ("SymToExpExpo", \ n -> symTopoToExpTopoPt (cakeParentsSymExpo n) |= cakeForm n, [4..9] )
    ] )
  where
    mybench (name,f,range) = bgroup name $ map (run f) range
    run f k = bench (show k) $ whnf f k

    myConfig = defaultConfig { Criterion.Types.csvFile = Just theCSVname }

-- Convert the .csv file to a .dat file to be use with pgfplots. (from SMCDEL)
convertMain :: IO ()
convertMain = do
  putStrLn "Reading bench-cake.csv and converting to .dat for pgfplots."
  c <- BL.readFile theCSVname
  case decode NoHeader c of
    Left e -> error $ "could not parse the csv file:" ++ show e
    Right csv -> do
      let results = map (parseLine . take 2) $ tail $ V.toList (csv :: V.Vector [String])
      let columns = nub.sort $ map (fst.fst) results
      let firstLine = longifyTo 5 "n" ++ dropWhileEnd isSpace (concatMap longify columns)
      let resAt n col = longify $ fromMaybe "nan" $ Data.List.lookup (col,n) results
      let resultrow n = concatMap (resAt n) columns
      let firstcol = nub.sort $ map (snd.fst) results
      let resultrows = map (\n -> longifyTo 5 (show n) ++ dropWhileEnd isSpace (resultrow n)) firstcol
      writeFile (theCSVname ++ ".dat") (intercalate "\n" (firstLine:resultrows) ++ "\n")
  where
    parseLine [namestr,numberstr] = case splitOn "/" namestr of
      [name,nstr] -> ((name,n),valuestr) where
        n = read nstr :: Integer
        value = toRealFloat (read numberstr :: Scientific) :: Double
        valuestr = Numeric.showFFloat (Just 7) value ""
      _ -> error $ "could not parse this case: " ++ namestr
    parseLine l = error $ "could not parse this line:\n  " ++ show l
    longify = longifyTo 14
    longifyTo n s = s ++ replicate (n - length s) ' '

-- CSV to pgfplots (from SMCDEL).

-- The filename to which the benchmark results will be written in CSV.
theCSVname :: String
theCSVname = "bench-cake.csv"

prepareMain :: IO ()
prepareMain = do
  oldResults <- doesFileExist theCSVname
  when oldResults $ do
    putStrLn "moving away old results!"
    renameFile theCSVname (theCSVname ++ ".OLD")
    oldDATfile <- doesFileExist (theCSVname ++ ".dat")
    when oldDATfile $ removeFile (theCSVname ++ ".dat")

-- Specification Formula.
cakeForm :: Int -> Form
cakeForm n = Conj [ante, Neg $ B (S.fromList (map show is)) (Neg consequent) ] where
    is = [1..n]
    phi js = Conj [ Neg (PrpF (P j)) | j <- js ]
    ante = Conj [ K (S.fromList (map show js)) (phi js) | js <- delete [] (powerset is) ]
    consequent = Conj [ phi js | js <- delete [] (powerset is) ]

-- Explicit model, linear variant.

-- Explicit model, linear: one child or no child ate cake.
cakeParents :: Int -> PtTopoEModel
cakeParents n = ( TopoEModel
    { space = S.fromList [0..n]
    , subb = M.fromList [(show k, S.fromList [S.fromList (delete k [0..n])]) | k <- [1..n] ]
    , part = M.fromList [(show k, S.fromList [S.fromList [0..n] ]) | k <- [1..n]] -- No hard evidence.
    , val = IntMap.fromList [ (w, M.fromList ( (P w, True) : [ (P k, False) | k <- delete w [0..n] ] ) )
                            | w <- [0..n] ]
    }
    , 0) -- Actually, nobody ate cake.

-- Explicit model, exponential variant.

{-
  Given n children, get the valuations for the (2^n) worlds by indexing the
  powerset of children (propositions) with numbers 1..2^n (worlds).
-}
cakeValExpo :: Int -> Valuation
cakeValExpo n = IntMap.fromList $ zip [0..] (map valsFor zeroInFront) where
  allKids = [1..n]
  zeroInFront = [] : delete [] (powerset allKids)
  valsFor is = M.fromList ([(P i, True) | i <- is] ++ [(P i, False) | i <- allKids \\ is])

-- Given a child i and a valuation, get indices of states in which child i ate cake.
evidenceAgainst :: Int -> Valuation -> [World]
evidenceAgainst i = IntMap.keys . IntMap.filter  (\k -> k M.! P i)

-- Explicit model, exponential: subgroups could have eaten cake.
cakeParentsExpo :: Int -> PtTopoEModel
cakeParentsExpo n = ( TopoEModel
    { space = S.fromList [0..(2^(n-1))]
    , subb = M.fromList [(show k,
        S.fromList [S.fromList ([0..(2^(n-1))] \\ evidenceAgainst k (cakeValExpo n))]) | k <- [1..n] ]
    , part = M.fromList [(show k, S.fromList [S.fromList [0..2^n]]) | k <- [1..n]] -- No hard evidence.
    , val = cakeValExpo n
    }
    , 0) -- Actually, nobody ate cake.

test :: Int -> Bool
test n = cakeParents n |= cakeForm n

testSymExpo :: Int -> Bool
testSymExpo n = cakeParentsSymExpo n |= cakeForm n

testExpo :: Int -> Bool
testExpo n = cakeParentsExpo n |= cakeForm n

testViaConv :: Int -> Bool
testViaConv n = expTopoToSymTopoPt (cakeParents n) |= cakeForm n

-- Symbolic structure, linear variant.

-- Symbolic structure, linear: one child or no child ate cake.
cakeParentsSym :: Int -> PtSymTopoEModel
cakeParentsSym n = (SymTEM
  { vocab = P 0 : map P [1..n]                                                         -- Who ate the cake?
                ++ map P [(n+1)..(n+n+1)]                                              -- Evidence pieces + 1 observable of the full space (partition).
  , theta = orB [ var k | k <- [0..n] ] .&&.                                           -- Someone or no one ate cake.
            andB [ notB (var k .&&. var j) | k <- [1..n], j <- delete k [0..n] ] .&&.  -- Only one child could have eaten cake.
            andB (var (n+n+1) : [ var (n+k) .<=>. notB (var k) | k <- [1..n] ])        -- Ev for i not eating cake is true iff i did not eat cake; prop representing full space is true.
  , evidence = M.fromList [(show i,[P (n + i)]) | i <- [1..n]]                         -- Each i has evidence for i not eating cake.
  , obs = M.fromList [(show i,[P (n+n+1)]) | i <- [1..n]]                              -- Partition is {X} (only one cell, which is the full space).
  }
  , P 0 : map P [(n+1)..(n+n+1)]                                                       -- Actually, no one ate cake.
  )

-- Symbolic structure, exponential: subgroups could have eaten cake.
cakeParentsSymExpo :: Int -> PtSymTopoEModel
cakeParentsSymExpo n = (SymTEM
  { vocab = map P [0..n]                                                               -- Who ate the cake?
                ++ map P [(n+1)..(n+n+1)]                                              -- Evidence pieces (P (n^2)+i = evidence that i didn't eat the cake) + 1 observable of the full space (partition).
  , theta = orB [ var k | k <- [0..n] ] .&&.                                           -- Someone or more than one or no one ate cake.
            andB (var (n+n+1) :  [ var (n+k) .<=>. notB (var k) | k <- [1..n]])        -- Ev for i not eating cake is true iff i did not eat cake; prop representing full space is true.
  , evidence = M.fromList [(show i,[P (n + i)]) | i <- [1..n]]                         -- Each i has evidence for i not eating cake.
  , obs = M.fromList [(show i,[P (n+n+1)]) | i <- [1..n]]                              -- Partition is {X} (only one cell, which is the full space).
  }
  , P 0 : map P [(n+1)..(n+n+1)]                                                       -- Actually, no one ate cake.
  )