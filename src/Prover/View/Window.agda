module Prover.View.Window where

open import Prover.Editor
  using (ViewStack)
open import Prover.Editor.Flat
  using (FlatViewStack)
open import Prover.Editor.Flatten
  using (view-stack-flatten)
open import Prover.View.Command
  using (Command; CommandPath)
open import Prover.View.Line
  using (Line; LinePath)
open import Prover.Prelude

-- ## Definitions

record Window
  : Set
  where

  constructor

    window

  field

    {length}
      : ℕ

    name
      : String

    -- Determines whether red or green light is shown in status bar.
    status
      : Bool

    lines
      : Vec Line length

data WindowPath
  (w : Window)
  : Set
  where

  go
    : (k : Fin (Window.length w))
    → LinePath (Window.lines w ! k)
    → WindowPath w

-- ## Stacks

WindowViewStack
  : ViewStack
WindowViewStack
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

WindowFlatViewStack
  : FlatViewStack
WindowFlatViewStack
  = view-stack-flatten
    WindowViewStack

