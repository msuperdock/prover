module Prover.Event.Proof.Meta where

open import Event.Nat
  using (NatEvent)

open import Prover.Event.Formula
  using (FormulaEvent)

-- ## Definitions

data ProofMetaMode
  : Set
  where

  nat
    : ProofMetaMode

  formula
    : ProofMetaMode

ProofMetaEvent
  : ProofMetaMode
  → Set
ProofMetaEvent nat
  = NatEvent
ProofMetaEvent formula
  = FormulaEvent

