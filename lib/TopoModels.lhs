\section{TopoModels}\label{sec:TopoModels}

\begin{code}

module TopoModels where

import Syntax (Form)
import Topology (TopoSpace)


type Valuation a = Form -> [a]

data TopoModel a = TopoModel (TopoSpace a) (Valuation a)

data PointedTopoModel a = PointedTopoModel (TopoModel a) a

\end{code}
