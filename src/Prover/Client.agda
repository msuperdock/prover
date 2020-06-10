module Prover.Client where

open import Prover.Client.Brick
  using (InputEvent; Widget)
open import Prover.Client.Event
  using (SpecialEvent)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Prelude

record Client
  (V : ViewStack)
  (E : EventStack)
  : Set
  where

  open ViewStack V
  open EventStack E

  field

    draw
      : (v : View)
      → ViewPath v
      → Widget

    draw-inner
      : (v : View)
      → (vp : ViewPath v)
      → (v' : ViewInner v vp)
      → ViewInnerPath v vp v'
      → Widget

    handle
      : (m : Mode)
      → InputEvent
      → Maybe (Event m ⊔ SpecialEvent)

    handle-inner
      : (m : ModeInner)
      → InputEvent
      → Maybe (EventInner m ⊔ SpecialEvent)

