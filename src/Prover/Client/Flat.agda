module Prover.Client.Flat where

open import Prover.Client.Brick
  using (InputEvent; Widget)
open import Prover.Client.Event
  using (SpecialEvent)
open import Prover.Editor.Flat
  using (FlatEventStack; FlatViewStack)
open import Prover.Prelude

-- ## FlatClient

record FlatClient
  (V : FlatViewStack)
  (E : FlatEventStack)
  : Set
  where

  open FlatViewStack V
  open FlatEventStack E

  field

    draw
      : (v : View)
      → ViewPath v
      → Widget

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)

