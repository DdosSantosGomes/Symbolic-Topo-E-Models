\section{Semantics}\label{sec:Semantics}

In this section we define the semantics for the formulas defined in \verb|Syntax.lhs| on both \verb|TopoModel|'s and \verb|S4KripkeModel|'s. \\

\begin{code}

module Semantics where

import qualified Data.Set as S

import KripkeModels (PointedS4KripkeModel (PS4KM), S4KripkeFrame (S4KF), S4KripkeModel (S4KM))
import SetTheory (imageIn)
import Syntax (Form (..))
import TopoModels (PointedTopoModel (..), TopoModel (..))
import Topology (TopoSpace (TopoSpace), openNbds)

\end{code}

Given a formula $\varphi$ in our language along with a model $\M$, a \emph{semantics} is a definition of when $\M$ makes $\varphi$ \emph{true}.
The relation `makes true' is often written using `$\models$', so we abbreviate the statement `$\M$ makes $\varphi$ true' as `$\M \models \varphi$'. \\

\begin{code}

class Semantics m where
    (|=) :: m -> Form -> Bool

\end{code}

In both of the below-defined instances of \verb|Semantics|, the Boolean cases are defined in the same, standard way, so we will only comment on the key modal cases.
For the Boolean cases, see \cite[pp. 17-18]{Bla01}.

\subsection{Kripke semantics}

Given a \emph{pointed} $\SFour$ Kripke model $(X, R, V, x)$, we define the following for all formulas $\varphi$ in our modal language.
\begin{align*}
  (X, R, V, x) \models \Box \varphi ~&:\Longleftrightarrow~ \forall y \in X (xRy \mimp (X, R, V, y) \models \varphi) \\
  (X, R, V, x) \models \Dia \varphi ~&:\Longleftrightarrow~ (X, R, V, x) \models \neg \Box \neg \varphi
\end{align*}

Given an $\SFour$ Kripke model $(X, R, V)$ (without a point), we also define the following for all formulas $\varphi$ in our modal language.
  \[ (X, R, V) \models \varphi ~:\Longleftrightarrow~ \forall x \in X ((X, R, V, x) \models \varphi) \]

\begin{code}

instance (Eq a, Ord a) => Semantics (PointedS4KripkeModel a) where
    (|=) _ Top = True
    (|=) _ Bot = False
    (|=) pointedModel (P n) = x `elem` worldsWherePnTrue
      where
        PS4KM kripkeModel x = pointedModel
        S4KM _ valuation = kripkeModel
        worldsWherePnTrue = snd . S.elemAt 0 $ S.filter (\(p, _) -> p == P n) valuation
    (|=) pointedModel (phi `Dis` psi) = (pointedModel |= phi) || (pointedModel |= psi)
    (|=) pointedModel (phi `Con` psi) = (pointedModel |= phi) && (pointedModel |= psi)
    (|=) pointedModel (phi `Imp` psi) = pointedModel |= (Neg phi `Dis` psi)
    (|=) pointedModel (Neg phi) = not $ pointedModel |= phi
    (|=) pointedModel (Dia phi) = pointedModel |= Neg (Box (Neg phi))
    (|=) pointedModel (Box phi) = all (\w' -> PS4KM kripkeModel w' |= phi) imageOfWorld
      where
        (PS4KM kripkeModel world) = pointedModel
        S4KM kripkeFrame _ = kripkeModel
        S4KF _ relation = kripkeFrame
        imageOfWorld = world `imageIn` relation

instance (Eq a, Ord a) => Semantics (S4KripkeModel a) where
    kripkeModel |= phi = wholeSetSatisfiesForm carrier phi
      where
        (S4KM frame _) = kripkeModel
        (S4KF carrier _) = frame
        wholeSetSatisfiesForm set psi = all (\x -> PS4KM kripkeModel x |= psi) set

\end{code}

\subsection{Topo-semantics}


Given a \emph{pointed} topomodel $(X, \tau, V, x)$, we define the following for all formulas $\varphi$ in our modal language.
\begin{align*}
  (X, R, V, x) \models \Box \varphi ~&:\Longleftrightarrow~ \exists U \in \tau (x \in U \text{ and } \forall y \in U ((X, \tau, V, y) \models \varphi))\\
  (X, \tau, V, x) \models \Dia \varphi ~&:\Longleftrightarrow~ (X, \tau, V, x) \models \neg \Box \neg \varphi
\end{align*}

Given a topomodel $(X, \tau, V)$ (without a point), we also define the following for all formulas $\varphi$ in our modal language.
  \[ (X, \tau, V) \models \varphi ~:\Longleftrightarrow~ \forall x \in X ((X, \tau, V, x) \models \varphi) \]


\begin{code}

instance (Eq a) => Semantics (PointedTopoModel a) where
    (|=) _ Top = True
    (|=) _ Bot = False
    (|=) pointedModel (P n) = x `elem` worldsWherePnTrue
      where
        PointedTopoModel topoModel x = pointedModel
        TopoModel _ valuation = topoModel
        worldsWherePnTrue = snd . S.elemAt 0 $ S.filter (\(p, _) -> p == P n) valuation
    (|=) pointedModel (phi `Dis` psi) = (pointedModel |= phi) || (pointedModel |= psi)
    (|=) pointedModel (phi `Con` psi) = (pointedModel |= phi) && (pointedModel |= psi)
    (|=) pointedModel (phi `Imp` psi) = pointedModel |= (Neg phi `Dis` psi)
    (|=) pointedModel (Neg phi) = not $ pointedModel |= phi
    (|=) pointedModel (Dia phi) = pointedModel |= Neg (Box (Neg phi))
    (|=) pointedModel (Box phi) = not (null openNbdsSatisfyingFormula)
      where
        PointedTopoModel topoModel point = pointedModel
        TopoModel topoSpace _ = topoModel
        wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x |= psi) set
        openNbdsOfPoint = openNbds point topoSpace
        openNbdsSatisfyingFormula = S.filter (`wholeSetSatisfiesForm` phi) openNbdsOfPoint

instance (Eq a) => Semantics (TopoModel a) where
    topoModel |= phi = wholeSetSatisfiesForm space phi
      where
        (TopoModel topoSpace _) = topoModel
        TopoSpace space _ = topoSpace
        wholeSetSatisfiesForm set psi = all (\x -> PointedTopoModel topoModel x |= psi) set

\end{code}

