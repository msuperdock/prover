module Prover.View.Proof where

open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Window
  using (Window; WindowPath)

-- ## Definitions

data ProofViewInner
  : Set
  where

  window
    : Window
    → ProofViewInner

  command
    : Command
    → ProofViewInner

  both
    : Window
    → Command
    → ProofViewInner

data ProofViewInnerPath
  : ProofViewInner
  → Set
  where

  window
    : {w : Window}
    → WindowPath w
    → ProofViewInnerPath (window w)

  command
    : {c : Command}
    → CommandPath c
    → ProofViewInnerPath (command c)

  both
    : {w : Window}
    → {c : Command}
    → CommandPath c
    → ProofViewInnerPath (both w c)

