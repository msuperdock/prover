module Prover.View.Tree where

open import Prover.Data.Fin
  using (Fin)
open import Prover.Data.List
  using (List; _!_)
open import Prover.View.Line
  using (Line)

-- ## Definitions

data Tree
  : Set
  where

  leaf
    : Line
    → Tree

  node
    : List Tree
    → Line
    → Tree

data TreePath
  : Tree
  → Set
  where

  stop
    : {t : Tree}
    → TreePath t

  go
    : {ts : List Tree}
    → {l : Line}
    → (k : Fin (List.length ts))
    → TreePath (ts ! k)
    → TreePath (node ts l)

