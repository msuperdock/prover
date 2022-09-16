module Prover.Stack.Formula where

open import Stack
  using (EventStack; ViewStack)
open import Event.Text
  using (TextEvent)

open import Prover.Data.Unit
  using (⊤)
open import Prover.Event.Formula
  using (FormulaEvent)
open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Formula
  using (FormulaView; FormulaViewPath)

-- ## Stacks

-- ### ViewStack

view-stack-formula
  : ViewStack
view-stack-formula
  = record
  { View
    = FormulaView
  ; ViewPath
    = FormulaViewPath
  ; ViewInner
    = λ _ _ → Command
  ; ViewInnerPath
    = λ _ _ → CommandPath
  }

-- ### EventStack

event-stack-formula
  : EventStack
event-stack-formula
  = record
  { Mode
    = ⊤
  ; ModeInner
    = ⊤
  ; Event
    = λ _ → FormulaEvent
  ; EventInner
    = λ _ → TextEvent
  }

