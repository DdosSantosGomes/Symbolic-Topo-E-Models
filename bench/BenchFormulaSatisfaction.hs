{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchFormulaSatisfaction where

import BenchHelpers (formSize, printAndAppendToFile)
import KripkeModels (
  PointedS4KripkeModel (..),
  S4KripkeFrame (S4KF),
  S4KripkeModel (S4KM),
 )
import ModelConversion (toPointedTopoModel)
import Semantics (Semantics ((|=)))
import TopoModels (
  PointedTopoModel (PointedTopoModel),
  TopoModel (TopoModel),
 )
import Topology (TopoSpace (TopoSpace))

import Data.Time (diffUTCTime, getCurrentTime, getZonedTime)
import Test.QuickCheck (Arbitrary (arbitrary), generate)
import Text.Printf (printf)

import Data.Set qualified as S

modelSatisfactionTimeThis :: String -> Int -> IO ()
modelSatisfactionTimeThis fileName n = do
  print n
  (s4km :: PointedS4KripkeModel Int) <- generate arbitrary
  let tm = toPointedTopoModel s4km
  f <- generate arbitrary

  -- Run the formula satisfaction experiments
  start <- getCurrentTime
  let resS4KM = s4km |= f
  end <- getCurrentTime
  let s4Time = end `diffUTCTime` start
  printf "\nS4KM: %.11f\n" (realToFrac s4Time :: Double)

  start2 <- getCurrentTime
  let resTM = tm |= f
  end2 <- getCurrentTime
  let tmTime = end2 `diffUTCTime` start2
  printf "TM:   %.11f\n" (realToFrac tmTime :: Double)

  if resS4KM == resTM
    then do
      -- Record the results
      let (PS4KM (S4KM (S4KF _ relations) _) _) = s4km
      let (PointedTopoModel (TopoModel (TopoSpace _ topology) _) _) = tm
      let resultString =
            show (S.size relations)
              ++ ","
              ++ show (S.size topology)
              ++ ","
              ++ show (formSize f)
              ++ ","
              ++ (printf "%.11f" (realToFrac s4Time :: Double) :: String)
              ++ ","
              ++ (printf "%.11f" (realToFrac tmTime :: Double) :: String)
              ++ "\n"
      printAndAppendToFile fileName resultString
    else do
      -- If the result is wrong for some reason, output variables values for debugging
      print f >> print s4km >> print tm >> print resS4KM >> print resTM

      let resultString = "Wrong result.\n"
      printAndAppendToFile fileName resultString

mainLoop :: [Int] -> String -> IO ()
mainLoop [] _ = putStrLn ""
mainLoop (n : ns) fileName = do
  modelSatisfactionTimeThis fileName n
  mainLoop ns fileName

main :: IO ()
main = do
  currentTime' <- getZonedTime
  let currentTime = show currentTime'
  let fileName = "formula-satisfaction-" ++ currentTime ++ ".csv"
  let header = "size_s4km,size_tm,size_form,time_s4,time_tm\n"
  putStrLn header
  writeFile fileName header

  -- Run the experiments 1000 times. Will be useful to plot a boxplot after
  mainLoop [1 .. 1000] fileName
