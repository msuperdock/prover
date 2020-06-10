module Prover.Editor where

open import Prover.Category
  using (Category)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

record ViewStack
  : Set₁
  where

  field

    View
      : Set

    ViewPath
      : View
      → Set
    
    ViewInner
      : (v : View)
      → ViewPath v
      → Set

    ViewInnerPath
      : (v : View)
      → (vp : ViewPath v)
      → ViewInner v vp
      → Set

-- ### EventStack

record EventStack
  : Set₁
  where

  field

    Mode
      : Set

    ModeInner
      : Set

    Event
      : Mode
      → Set

    EventInner
      : ModeInner
      → Set

-- ## StackMaps

-- ### ViewStackMap

-- #### Definition

record ViewStackMap
  (V W : ViewStack)
  : Set
  where

  field

    view
      : ViewStack.View V
      → ViewStack.View W

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View W
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath W
        (view-with v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner W
        (view-with v vp)
        (view-path v vp)

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath W
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')

-- #### Compose

module _
  {V W X : ViewStack}
  where

  module ViewStackMapComposeWith
    (F : ViewStack.View V → ViewStackMap W X)
    (G : ViewStackMap V W)
    where

    view
      : ViewStack.View V
      → ViewStack.View X
    view v
      = ViewStackMap.view (F v)
        (ViewStackMap.view G v)

    view-with
      : (v : ViewStack.View V)
      → ViewStack.ViewPath V v
      → ViewStack.View X
    view-with v vp
      = ViewStackMap.view-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
    
    view-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → ViewStack.ViewPath X
        (view-with v vp)
    view-path v vp
      = ViewStackMap.view-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)

    view-inner-with
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → ViewStack.ViewInnerPath V v vp v'
      → ViewStack.ViewInner X
        (view-with v vp)
        (view-path v vp)
    view-inner-with v vp v' vp'
      = ViewStackMap.view-inner-with (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

    view-inner-path
      : (v : ViewStack.View V)
      → (vp : ViewStack.ViewPath V v)
      → (v' : ViewStack.ViewInner V v vp)
      → (vp' : ViewStack.ViewInnerPath V v vp v')
      → ViewStack.ViewInnerPath X
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path v vp v' vp'
      = ViewStackMap.view-inner-path (F v)
        (ViewStackMap.view-with G v vp)
        (ViewStackMap.view-path G v vp)
        (ViewStackMap.view-inner-with G v vp v' vp')
        (ViewStackMap.view-inner-path G v vp v' vp')

  view-stack-map-compose-with
    : (ViewStack.View V → ViewStackMap W X)
    → ViewStackMap V W
    → ViewStackMap V X
  view-stack-map-compose-with F G
    = record {ViewStackMapComposeWith F G}

-- ### EventStackMap

record EventStackMap
  (E F : EventStack)
  : Set
  where

  field

    mode
      : EventStack.Mode E
      → EventStack.Mode F

    mode-inner
      : EventStack.ModeInner E
      → EventStack.ModeInner F

    event
      : (m : EventStack.Mode E)
      → EventStack.Event F (mode m)
      → EventStack.Event E m

    event-inner
      : (m : EventStack.ModeInner E)
      → EventStack.EventInner F (mode-inner m)
      → EventStack.EventInner E m

-- ## Editors

-- ### Editor

record Editor
  (V : ViewStack)
  (E : EventStack)
  (C : Category)
  : Set₁
  where
 
  -- #### Types

  open ViewStack V
  open EventStack E

  open Category C using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity
      to state-identity
    ; compose
      to state-compose
    ; precompose
      to state-precompose
    ; postcompose
      to state-postcompose
    ; associative
      to state-associative
    )

  -- #### State

  field

    StatePath
      : State
      → Set

    StateInner
      : (s : State)
      → StatePath s
      → Set

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set

  StateStack
    : ViewStack
  StateStack
    = record
    { View
      = State
    ; ViewPath
      = StatePath
    ; ViewInner
      = StateInner
    ; ViewInnerPath
      = StateInnerPath
    }

  field

    initial
      : State

    -- The initial path when entering from the given direction.
    initial-path
      : (s : State)
      → Direction
      → StatePath s

  -- #### Draw

  field

    draw-stack
      : ViewStackMap StateStack V

  open ViewStackMap draw-stack public using () renaming
    ( view
      to draw
    ; view-with
      to draw-with
    ; view-path
      to draw-path
    ; view-inner-with
      to draw-inner-with
    ; view-inner-path
      to draw-inner-path
    )

  -- #### Mode

  field

    mode
      : (s : State)
      → StatePath s
      → Mode

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner

  -- #### Handle

  field

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)

    handle-direction-valid
      : (s : State)
      → (d : Direction)
      → handle-direction s (initial-path s d) d ≡ nothing

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'

-- ### SimpleEditor

data SimpleEditor
  (V : ViewStack)
  (E : EventStack)
  : Set
  → Set₁
  where

  simple-editor
    : {C : Category}
    → Editor V E C
    → SimpleEditor V E (Category.Object C)

-- ### PartialEditor

record PartialEditor
  (V : ViewStack)
  (E : EventStack)
  (A : Set)
  : Set₁
  where

  constructor

    partial-editor

  field

    {StateCategory}
      : Category

  open Category StateCategory public using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity
      to state-identity
    ; compose
      to state-compose
    ; precompose
      to state-precompose
    ; postcompose
      to state-postcompose
    ; associative
      to state-associative
    )

  field

    editor
      : Editor V E StateCategory

  open Editor editor public

  field

    base
      : State
      → Maybe A

  is-complete
    : State
    → Bool
  is-complete s
    = Maybe.is-just (base s)

-- ### SplitEditor

-- #### Definition

record SplitEditor
  (V : ViewStack)
  (E : EventStack)
  (C : Category)
  : Set₁
  where

  constructor

    split-editor

  field

    {StateCategory}
      : Category

  open Category StateCategory public using () renaming
    ( Object
      to State
    ; Arrow
      to StateArrow
    ; identity
      to state-identity
    ; compose
      to state-compose
    ; precompose
      to state-precompose
    ; postcompose
      to state-postcompose
    ; associative
      to state-associative
    )

  field

    editor
      : Editor V E StateCategory

  open Editor editor public

  field

    split-functor
      : SplitFunctor StateCategory C

  open SplitFunctor split-functor public

  is-complete
    : State
    → Bool
  is-complete s
    = Maybe.is-just (base s)

  draw-pure
    : Category.Object C
    → ViewStack.View V
  draw-pure x
    = draw (unbase x)

-- #### Conversion

split-editor-partial
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → SplitEditor V E C
  → PartialEditor V E (Category.Object C)
split-editor-partial e
  = record {SplitEditor e}

