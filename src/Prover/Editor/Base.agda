module Prover.Editor.Base where

open import Prover.Category
  using (Category)
open import Prover.Prelude

-- ## Stacks

-- ### BaseViewStack

record BaseViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set

-- ### BaseEventStack

record BaseEventStack
  : Set₁
  where

  field

    Mode
      : Set

    Event
      : Mode
      → Set

-- ## StackMaps

-- ### BaseViewStackMap

record BaseViewStackMap
  (V W : BaseViewStack)
  : Set
  where

  field

    view
      : BaseViewStack.View V
      → BaseViewStack.View W

    view-with
      : (v : BaseViewStack.View V)
      → BaseViewStack.ViewPath V v
      → BaseViewStack.View W
    
    view-path
      : (v : BaseViewStack.View V)
      → (vp : BaseViewStack.ViewPath V v)
      → BaseViewStack.ViewPath W (view-with v vp)

-- ### BaseEventStackMap

record BaseEventStackMap
  (E F : BaseEventStack)
  : Set
  where

  field

    mode
      : BaseEventStack.Mode E
      → BaseEventStack.Mode F

    event
      : (m : BaseEventStack.Mode E)
      → BaseEventStack.Event F (mode m)
      → BaseEventStack.Event E m

-- ## Editors

-- ### BaseEditor

record BaseEditor
  (V : BaseViewStack)
  (E : BaseEventStack)
  (C : Category)
  : Set₁
  where

  -- #### Types

  open BaseViewStack V
  open BaseEventStack E

  open Category C using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    )

  -- #### State

  field

    StatePath
      : State
      → Set

  StateStack
    : BaseViewStack
  StateStack
    = record
    { View
      = State
    ; ViewPath
      = StatePath
    }

  field

    initial
      : State

    initial-path
      : (s : State)
      → StatePath s

    -- The initial path when entering from the given direction.
    initial-path-with
      : (s : State)
      → Direction
      → StatePath s

  -- #### Draw

  field

    draw
      : State
      → View

    draw-with
      : (s : State)
      → StatePath s
      → View

    draw-path
      : (s : State)
      → (sp : StatePath s)
      → ViewPath (draw-with s sp)

  draw-stack
    : BaseViewStackMap StateStack V
  draw-stack
    = record
    { view
      = draw
    ; view-with
      = draw-with
    ; view-path
      = draw-path
    }

  -- #### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

  -- #### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing

-- ### SimpleBaseEditor

record SimpleBaseEditor
  (V : BaseViewStack)
  (E : BaseEventStack)
  (A : Set)
  : Set₁
  where

  -- ##### Types

  open BaseViewStack V
  open BaseEventStack E

  private

    State
      : Set
    State
      = A

  -- ##### State

  field

    StatePath
      : State
      → Set

  StateStack
    : BaseViewStack
  StateStack
    = record
    { View
      = State
    ; ViewPath
      = StatePath
    }

  field

    initial
      : State

    initial-path
      : (s : State)
      → StatePath s

    -- The initial path when entering from the given direction.
    initial-path-with
      : (s : State)
      → Direction
      → StatePath s

  -- ##### Draw

  field

    draw
      : State
      → View

    draw-with
      : (s : State)
      → StatePath s
      → View

    draw-path
      : (s : State)
      → (sp : StatePath s)
      → ViewPath (draw-with s sp)

  draw-stack
    : BaseViewStackMap StateStack V
  draw-stack
    = record
    { view
      = draw
    ; view-with
      = draw-with
    ; view-path
      = draw-path
    }

  -- ##### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

  -- ##### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path-with s d) d ≡ nothing

