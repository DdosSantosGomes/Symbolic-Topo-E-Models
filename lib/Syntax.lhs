\section{Syntax}\label{sec:Syntax}

\begin{code}
module Syntax where

import Test.QuickCheck
\end{code}


\begin{code}
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

\begin{code}
instance Arbitrary Form where
  arbitrary = sized randomForm
   where
    randomForm :: Int -> Gen Form
    randomForm 0 = P <$> elements [1 .. 5]
    randomForm n =
      oneof
        [
        P <$> elements [1 .. 5]
        , Dis
            <$> randomForm (n `div` 2)
            <*> randomForm (n `div` 2)
        , Con
            <$> randomForm (n `div` 2)
            <*> randomForm (n `div` 2)
        , Imp
            <$> randomForm (n `div` 2)
            <*> randomForm (n `div` 2)
        , Neg <$> randomForm (n `div` 2)
        , Dia <$> randomForm (n `div` 2)
        , Box <$> randomForm (n `div` 2)
        ]
\end{code}