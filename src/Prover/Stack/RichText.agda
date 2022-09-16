module Prover.Stack.RichText where

open import Stack
  using (ViewStack)
open import Stack.Lift
  using (view-stack-lift)

open import Prover.Stack.Base.RichText
  using (base-view-stack-rich-text)

-- ## Stacks

-- ### ViewStack

view-stack-rich-text
  : ViewStack
view-stack-rich-text
  = view-stack-lift
    base-view-stack-rich-text

