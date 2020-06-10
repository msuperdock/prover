module Prover.Editor.Lift where

open import Prover.Category
  using (Category)
open import Prover.Editor
  using (Editor; EventStack; EventStackMap; SimpleEditor; ViewStack;
    ViewStackMap; simple-editor)
open import Prover.Editor.Base
  using (BaseEditor; BaseEventStack; BaseEventStackMap; BaseViewStack;
    BaseViewStackMap; SimpleBaseEditor; base-editor-from-simple)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

module ViewStackLift
  (V : BaseViewStack)
  where

  open BaseViewStack V public
    using (View; ViewPath)

  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner _ _
    = ⊥

  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath _ _ ()

view-stack-lift
  : BaseViewStack
  → ViewStack
view-stack-lift V
  = record {ViewStackLift V}

-- ### EventStack

module EventStackLift
  (E : BaseEventStack)
  where

  open BaseEventStack E public

  ModeInner
    : Set
  ModeInner
    = ⊥

  EventInner
    : ModeInner
    → Set
  EventInner ()

event-stack-lift
  : BaseEventStack
  → EventStack
event-stack-lift E
  = record {EventStackLift E}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W : BaseViewStack}
  where

  module ViewStackMapLift
    (F : BaseViewStackMap V W)
    where

    open BaseViewStackMap F public

    view-inner-with
      : (v : ViewStack.View (view-stack-lift V))
      → (vp : ViewStack.ViewPath (view-stack-lift V) v)
      → (v' : ViewStack.ViewInner (view-stack-lift V) v vp)
      → ViewStack.ViewInnerPath (view-stack-lift V) v vp v'
      → ViewStack.ViewInner (view-stack-lift W)
        (view-with v vp)
        (view-path v vp)
    view-inner-with _ _ ()

    view-inner-path
      : (v : ViewStack.View (view-stack-lift V))
      → (vp : ViewStack.ViewPath (view-stack-lift V) v)
      → (v' : ViewStack.ViewInner (view-stack-lift V) v vp)
      → (vp' : ViewStack.ViewInnerPath (view-stack-lift V) v vp v')
      → ViewStack.ViewInnerPath (view-stack-lift W)
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path _ _ ()

  view-stack-map-lift
    : BaseViewStackMap V W
    → ViewStackMap
      (view-stack-lift V)
      (view-stack-lift W)
  view-stack-map-lift F
    = record {ViewStackMapLift F}

-- ### EventStackMap

module _
  {E F : BaseEventStack}
  where

  module EventStackMapLift
    (G : BaseEventStackMap E F)
    where

    open BaseEventStackMap G public

    mode-inner
      : EventStack.ModeInner (event-stack-lift E)
      → EventStack.ModeInner (event-stack-lift F)
    mode-inner ()

    event-inner
      : (m : EventStack.ModeInner (event-stack-lift E))
      → EventStack.EventInner (event-stack-lift F) (mode-inner m)
      → EventStack.EventInner (event-stack-lift E) m
    event-inner ()

  event-stack-map-lift
    : BaseEventStackMap E F
    → EventStackMap
      (event-stack-lift E)
      (event-stack-lift F)
  event-stack-map-lift G
    = record {EventStackMapLift G}

-- ## Editors

-- ### Editor

module _
  {V : BaseViewStack}
  {E : BaseEventStack}
  {C : Category}
  where

  -- #### Module

  module EditorLift
    (e : BaseEditor V E C)
    where

    -- ##### Types

    open ViewStack (view-stack-lift V)
    open EventStack (event-stack-lift E)

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

    -- ##### State

    open BaseEditor e public
      using (initial; initial-path; initial-path-with)

    StateStack
      : ViewStack
    StateStack
      = view-stack-lift
        (BaseEditor.StateStack e)

    open ViewStack StateStack public using () renaming
      ( ViewPath
        to StatePath
      ; ViewInner
        to StateInner
      ; ViewInnerPath
        to StateInnerPath
      )

    -- ##### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-lift V)
    draw-stack
      = view-stack-map-lift
        (BaseEditor.draw-stack e)

    -- ##### Mode

    open BaseEditor e public
      using (mode)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner _ _ ()

    -- ##### Handle

    open BaseEditor e public
      using (handle-direction; handle-direction-valid)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      = ι₁ (BaseEditor.handle e s sp e')

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape _ _
      = nothing

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return _ _
      = nothing

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner _ _ ()

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape _ _ ()

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return _ _ ()

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction _ _ ()

  -- #### Function

  editor-lift
    : BaseEditor V E C
    → Editor
      (view-stack-lift V)
      (event-stack-lift E) C
  editor-lift e
    = record {EditorLift e}

-- ### SimpleEditor

simple-editor-lift
  : {V : BaseViewStack}
  → {E : BaseEventStack}
  → {A : Set}
  → SimpleBaseEditor V E A
  → SimpleEditor
    (view-stack-lift V)
    (event-stack-lift E) A
simple-editor-lift e
  = simple-editor (editor-lift (base-editor-from-simple e))

