module Prover.Stack.Flat.Proof.Meta where

open import Stack.Flat
  using (FlatEventStack)

open import Prover.Event.Flat.Proof.Meta
  using (FlatProofMetaEvent; FlatProofMetaMode)

-- ## Stacks

-- ### FlatEventStack

flat-event-stack-proof-meta
  : FlatEventStack
flat-event-stack-proof-meta
  = record
  { Mode
    = FlatProofMetaMode
  ; Event
    = FlatProofMetaEvent
  }

