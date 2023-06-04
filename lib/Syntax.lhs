\section{Modal logic}\label{sec:Syntax}

In this section we define the syntax of a basic propositional modal logic. \\

\begin{code}
module Syntax where

import Test.QuickCheck
\end{code}

\subsection{Syntax}

Our language will be the formulas of the following shape.
    \[ \varphi := \top
             \mid \bot
             \mid p_n
             \mid \varphi \lor \varphi
             \mid \varphi \land \varphi
             \mid \varphi \imp \varphi
             \mid \neg \varphi
             \mid \Dia \varphi
             \mid \Box \varphi \]

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
    deriving (Eq, Show, Ord)

\end{code}

\subsection{Arbitrary modal formula generation}

When testing, we can generate arbitrary \verb|Form|'s via the following instance of \verb|Arbitrary|. \\

\begin{code}

instance Arbitrary Form where
    arbitrary = sized randomForm
      where
        randomForm :: Int -> Gen Form
        randomForm 0 = P <$> elements [1 .. 5] -- Fixed vocabulary
        randomForm n =
            oneof
                [ P <$> elements [1 .. 5]
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