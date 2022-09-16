module Prover.Event.Proof where

open import Event.Nat
  using (NatEvent)
open import Event.Text
  using (TextEvent)

open import Prover.Event.Formula
  using (FormulaEvent)

-- ## Definitions

data ProofModeInner
  : Set
  where

  text
    : ProofModeInner

  nat
    : ProofModeInner

  formula
    : ProofModeInner

data ProofEvent
  : Set
  where

  infer-hypotheses
    : ProofEvent

  substitute-meta
    : ProofEvent

ProofEventInner
  : ProofModeInner
  → Set
ProofEventInner text
  = TextEvent
ProofEventInner nat
  = NatEvent
ProofEventInner formula
  = FormulaEvent

