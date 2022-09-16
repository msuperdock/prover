module Prover.Stack.Flat.Command where

open import Stack.Flat
  using (FlatViewStack)

open import Prover.View.Command
  using (Command; CommandPath)

-- ## Stacks

-- ### FlatViewStack

flat-view-stack-command
  : FlatViewStack
flat-view-stack-command
  = record
  { View
    = Command
  ; ViewPath
    = CommandPath
  }

