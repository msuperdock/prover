module Prover.Stack.Proof.Meta where

open import Event.Text
  using (TextEvent)
open import Stack
  using (EventStack)

open import Prover.Data.Unit
  using (⊤)
open import Prover.Event.Proof.Meta
  using (ProofMetaEvent; ProofMetaMode)

-- ## Stacks

-- ### EventStack

event-stack-proof-meta
  : EventStack
event-stack-proof-meta
  = record
  { Mode
    = ProofMetaMode
  ; ModeInner
    = ⊤
  ; Event
    = ProofMetaEvent
  ; EventInner
    = λ _ → TextEvent
  }

