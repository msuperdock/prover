module Prover.Event.Flat.Proof.Meta where

open import Event.Nat
  using (NatEvent)
open import Event.Text
  using (TextEvent)

open import Prover.Event.Formula
  using (FormulaEvent)

-- ## Definitions

data FlatProofMetaMode
  : Set
  where

  text
    : FlatProofMetaMode

  nat
    : FlatProofMetaMode

  formula
    : FlatProofMetaMode

FlatProofMetaEvent
  : FlatProofMetaMode
  → Set
FlatProofMetaEvent text
  = TextEvent
FlatProofMetaEvent nat
  = NatEvent
FlatProofMetaEvent formula
  = FormulaEvent

