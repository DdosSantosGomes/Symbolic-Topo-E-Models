{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchModelConversion where

import BenchHelpers (printAndAppendToFile)
import KripkeModels (S4KripkeFrame (S4KF), S4KripkeModel (..))
import TopoModels (TopoModel (TopoModel))
import Topology (TopoSpace (TopoSpace))

import Data.Set qualified as S
import Data.Time (diffUTCTime, getCurrentTime, getZonedTime)

import ModelConversion (toS4KripkeModel, toTopoModel)
import Test.QuickCheck (Arbitrary (arbitrary), Gen, generate)
import Text.Printf (printf)

modelConversionTimeThis :: String -> Int -> IO ()
modelConversionTimeThis fileName n = do
  print n
  s4km <- generate (arbitrary :: Gen (S4KripkeModel Int))

  -- Run the model conversion experiments
  start <- getCurrentTime
  let tm = toTopoModel s4km
  end <- getCurrentTime
  let s4Time = end `diffUTCTime` start
  printf "\nS4KM -> TM: %.11f\n" (realToFrac s4Time :: Double)

  start2 <- getCurrentTime
  let s4kmBack = toS4KripkeModel tm
  end2 <- getCurrentTime
  let tmTime = end2 `diffUTCTime` start2
  printf "TM -> S4KM:   %.11f\n" (realToFrac tmTime :: Double)

  -- Record the results
  let (S4KM (S4KF _ relations) _) = s4km
  let (TopoModel (TopoSpace _ topology) _) = tm
  let (S4KM (S4KF _ relationsBack) _) = s4kmBack
  let resultString =
        show (S.size relations)
          ++ ","
          ++ show (S.size topology)
          ++ ","
          ++ show (S.size relationsBack)
          ++ ","
          ++ (printf "%.11f" (realToFrac s4Time :: Double) :: String)
          ++ ","
          ++ (printf "%.11f" (realToFrac tmTime :: Double) :: String)
          ++ "\n"
  printAndAppendToFile fileName resultString

mainLoop :: [Int] -> String -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n : ns) fileName = do
  modelConversionTimeThis fileName n
  mainLoop ns fileName

main :: IO ()
main = do
  currentTime' <- getZonedTime
  let currentTime = show currentTime'
  let fileName = "model-conversion-" ++ currentTime ++ ".csv"
  let header = "size_s4km,size_tm,size_s4kmBack,time_kmTotm,time_tmTokm\n"
  putStrLn header
  writeFile fileName header

  -- Run the experiments 1000 times. Will be useful to plot a boxplot after
  mainLoop [1 .. 1000] fileName