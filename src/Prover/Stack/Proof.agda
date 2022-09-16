module Prover.Stack.Proof where

open import Stack
  using (EventStack; ViewStack)

open import Prover.Data.List
  using (List)
open import Prover.Data.Unit
  using (⊤)
open import Prover.Event.Proof
  using (ProofEvent; ProofEventInner; ProofModeInner)
open import Prover.View.Line
  using (Line)
open import Prover.View.Proof
  using (ProofViewInner; ProofViewInnerPath)

-- ## Stacks

-- ### ViewStack

view-stack-proof
  : ViewStack
view-stack-proof
  = record
  { View
    = List Line
  ; ViewPath
    = λ _ → ⊤
  ; ViewInner
    = λ _ _ → ProofViewInner
  ; ViewInnerPath
    = λ _ _ → ProofViewInnerPath
  }

-- ### EventStack

event-stack-proof
  : EventStack
event-stack-proof
  = record
  { Mode
    = ⊤
  ; ModeInner
    = ProofModeInner
  ; Event
    = λ _ → ProofEvent
  ; EventInner
    = ProofEventInner
  }

