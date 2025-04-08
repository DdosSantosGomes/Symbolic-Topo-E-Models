module DD_Visual where

import Data.DecisionDiagram.BDD hiding (restrict)
import Data.GraphViz
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Types.Monadic
import Data.IntMap hiding (map)


{-
  Visualization of BDDs.
  Ideally some day this should be upstreamed to the `decision-diagrams` libary.
-}

-- An example Bdd
-- from https://github.com/DdosSantosGomes/Symbolic-Topology/actions/runs/11615312043/job/32345578959#step:5:17
example :: BDD AscOrder
example = fromGraph (Data.IntMap.fromList
  [(0, SLeaf False), (1, SLeaf True), (2, SBranch 8 1 0), (3, SBranch 7 2 0), (4, SBranch 6 3 0), (5, SBranch 7 0 2), (6, SBranch 6 0 5), (7, SBranch 5 4 6), (8, SBranch 8 0 1), (9, SBranch 7 8 0), (10, SBranch 6 9 0), (11, SBranch 6 0 9), (12, SBranch 5 10 11), (13, SBranch 3 7 12)], 13)

labelFor :: Show a => Sig a -> String
labelFor (SLeaf True) = "T"
labelFor (SLeaf False) = "F"
labelFor (SBranch v _ _) = show v

edgesFor :: Int -> Sig Int -> DotM Int ()
edgesFor _ (SLeaf True) = return ()
edgesFor _ (SLeaf False) = return ()
edgesFor n (SBranch _ a b) = do
  edge n a [style dashed] -- False edge is dashed.
  edge n b []

ddToGraphViz :: BDD a -> Data.GraphViz.Types.Generalised.DotGraph Int
ddToGraphViz b = digraph' $ do
  let g = fst (toGraph b)
  let fix | b == true = delete 0
          | b == false = delete 1
          | otherwise = id
  let nodes = (Data.IntMap.keys (fix g) :: [Int])
  mapM_ (\ n -> node n [toLabel $ labelFor $ (Data.IntMap.!) g n]) nodes
  mapM_ (\ n -> edgesFor n ((Data.IntMap.!) g n)) nodes

-- | Write the picture of given Bdd to "example.pdf".
pdfBdd :: BDD a -> IO FilePath
pdfBdd x = runGraphviz (ddToGraphViz x) Pdf "example.pdf"

-- | Show Bdd in a window. Might only work on Linux.
showBdd :: BDD a -> IO ()
showBdd x = runGraphvizCanvas Dot (ddToGraphViz x) Xlib
