module Prover.Stack.Window where

open import Stack
  using (ViewStack)

open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Window
  using (Window; WindowPath)

-- ## Stacks

-- ### ViewStack

view-stack-window
  : ViewStack
view-stack-window
  = record
  { View
    = Window
  ; ViewPath
    = WindowPath
  ; ViewInner
    = λ _ _ → Command
  ; ViewInnerPath
    = λ _ _ → CommandPath
  }

