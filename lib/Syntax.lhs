\section{Syntax}\label{sec:Syntax}

\begin{code}

module Syntax where

data Form
    = Top
    | Bot
    | P Int
    | Form `Dis` Form
    | Form `Con` Form
    | Form `Imp` Form
    | Neg Form
    | Dia Form
    | Box Form
    deriving (Eq, Show)

\end{code}
