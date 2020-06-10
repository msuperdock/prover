module Prover.Client.Flatten where

open import Prover.Client
  using (Client; SpecialEvent)
open import Prover.Client.Brick
  using (InputEvent; Widget)
open import Prover.Client.Flat
  using (FlatClient)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Flat
  using (FlatEventStack; FlatViewStack)
open import Prover.Editor.Flatten
  using (event-stack-flatten; view-stack-flatten)
open import Prover.Prelude

-- ## Client

module _
  {V : ViewStack}
  {E : EventStack}
  where

  module ClientFlatten
    (c : Client V E)
    where

    open FlatViewStack (view-stack-flatten V)
    open FlatEventStack (event-stack-flatten E)

    draw
      : (v : View)
      → ViewPath v
      → Widget
    draw (v , nothing)
      = Client.draw c v
    draw (v , just (vp , v'))
      = Client.draw-inner c v vp v'

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)
    handle (ι₁ m)
      = Client.handle c m
    handle (ι₂ m)
      = Client.handle-inner c m

  client-flatten
    : Client V E
    → FlatClient
      (view-stack-flatten V)
      (event-stack-flatten E)
  client-flatten c
    = record {ClientFlatten c}

