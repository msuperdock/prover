module Prover.Stack.Flat.Window where

open import Stack.Flat
  using (FlatViewStack)
open import Stack.Flatten
  using (view-stack-flatten)

open import Prover.Stack.Window
  using (view-stack-window)

-- ## Stacks

-- ### FlatViewStack

flat-view-stack-window
  : FlatViewStack
flat-view-stack-window
  = view-stack-flatten
    view-stack-window

