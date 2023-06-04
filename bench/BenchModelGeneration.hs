{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchModelGeneration where

import BenchHelpers (printAndAppendToFile)
import KripkeModels (
  PointedS4KripkeModel (..),
  S4KripkeFrame (S4KF),
  S4KripkeModel (S4KM),
 )
import TopoModels (PointedTopoModel (..), TopoModel (TopoModel))
import Topology (TopoSpace (TopoSpace))

import Data.Set qualified as S
import Data.Time (diffUTCTime, getCurrentTime, getZonedTime)

import Test.QuickCheck
import Text.Printf

modelGenerationTimeThis :: String -> Int -> IO ()
modelGenerationTimeThis fileName n = do
  print n
  -- Run the model generation experiments
  start <- getCurrentTime
  s4km <- generate (arbitrary :: Gen (PointedS4KripkeModel Int))
  end <- getCurrentTime
  let s4Time = end `diffUTCTime` start
  printf "\nS4KM: %.9f\n" (realToFrac s4Time :: Double)

  start2 <- getCurrentTime
  tm <- generate (arbitrary :: Gen (PointedTopoModel Int))
  end2 <- getCurrentTime
  let tmTime = end2 `diffUTCTime` start2
  printf "TM:   %.11f\n" (realToFrac tmTime :: Double)

  -- Record the results
  let (PS4KM (S4KM (S4KF _ relations) _) _) = s4km
  let (PointedTopoModel (TopoModel (TopoSpace _ topology) _) _) = tm
  let resultString =
        show (S.size relations)
          ++ ","
          ++ show (S.size topology)
          ++ ","
          ++ (printf "%.11f" (realToFrac s4Time :: Double) :: String)
          ++ ","
          ++ (printf "%.11f" (realToFrac tmTime :: Double) :: String)
          ++ "\n"
  printAndAppendToFile fileName resultString

mainLoop :: [Int] -> String -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n : ns) fileName = do
  modelGenerationTimeThis fileName n
  mainLoop ns fileName

main :: IO ()
main = do
  currentTime' <- getZonedTime
  let currentTime = show currentTime'
  let fileName = "model-generation-" ++ currentTime ++ ".csv"
  let header = "size_s4km,size_tm,time_s4km,time_tm\n"
  putStrLn header
  writeFile fileName header

  -- Run the experiments 1000 times. Will be useful to plot a boxplot after
  mainLoop [1 .. 1000] fileName