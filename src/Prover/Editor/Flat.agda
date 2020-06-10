module Prover.Editor.Flat where

open import Prover.Prelude

-- ## Stacks

-- ### FlatViewStack

record FlatViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set

-- ### FlatEventStack

record FlatEventStack
  : Set₁
  where

  field

    Mode
      : Set

    Event
      : Mode
      → Set

-- ## StackMaps

-- ### FlatViewStackMap

-- #### Definition

record FlatViewStackMap
  (V W : FlatViewStack)
  : Set
  where

  field

    view-with
      : (v : FlatViewStack.View V)
      → FlatViewStack.ViewPath V v
      → FlatViewStack.View W
    
    view-path
      : (v : FlatViewStack.View V)
      → (vp : FlatViewStack.ViewPath V v)
      → FlatViewStack.ViewPath W (view-with v vp)

-- #### Compose

module _
  {V W X : FlatViewStack}
  where

  module FlatViewStackMapCompose
    (F : FlatViewStackMap W X)
    (G : FlatViewStackMap V W)
    where

    view-with
      : (v : FlatViewStack.View V)
      → FlatViewStack.ViewPath V v
      → FlatViewStack.View X
    view-with v vp
      = FlatViewStackMap.view-with F
        (FlatViewStackMap.view-with G v vp)
        (FlatViewStackMap.view-path G v vp)
    
    view-path
      : (v : FlatViewStack.View V)
      → (vp : FlatViewStack.ViewPath V v)
      → FlatViewStack.ViewPath X (view-with v vp)
    view-path v vp
      = FlatViewStackMap.view-path F
        (FlatViewStackMap.view-with G v vp)
        (FlatViewStackMap.view-path G v vp)

  flat-view-stack-map-compose
    : FlatViewStackMap W X
    → FlatViewStackMap V W
    → FlatViewStackMap V X
  flat-view-stack-map-compose F G
    = record {FlatViewStackMapCompose F G}

-- ### FlatEventStackMap

record FlatEventStackMap
  (E F : FlatEventStack)
  : Set
  where

  field

    mode
      : FlatEventStack.Mode E
      → FlatEventStack.Mode F

    event
      : (m : FlatEventStack.Mode E)
      → FlatEventStack.Event F (mode m)
      → FlatEventStack.Event E m

-- ## Editor

record FlatEditor
  (V : FlatViewStack)
  (E : FlatEventStack)
  (A : Set)
  : Set₁
  where

  -- ### Types

  open FlatViewStack V
  open FlatEventStack E

  -- ### State

  field

    StateStack
      : FlatViewStack

  open FlatViewStack StateStack public using () renaming
    ( View
      to State
    ; ViewPath
      to StatePath
    )

  field

    initial
      : State

    initial-path
      : StatePath initial

  -- ### Draw

  field

    draw-stack
      : FlatViewStackMap StateStack V

  open FlatViewStackMap draw-stack public using () renaming
    ( view-with
      to draw-with
    ; view-path
      to draw-path
    )

  -- ### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

  -- ### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (Σ State StatePath)

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → A ⊔ Σ State StatePath

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → StatePath s

