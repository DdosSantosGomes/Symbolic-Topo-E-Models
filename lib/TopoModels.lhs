\section{TopoModels}\label{sec:TopoModels}

\begin{code}

module TopoModels where

import Data.Set (Set)

import Syntax (Form)
import Topology (TopoSpace)

type Valuation a = Set (Form, Set a)

data TopoModel a = TopoModel (TopoSpace a) (Valuation a)
    deriving (Eq, Show)

data PointedTopoModel a = PointedTopoModel (TopoModel a) a

\end{code}
