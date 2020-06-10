module Prover.Editor.Parent where

open import Prover.Category
  using (Category)
open import Prover.Editor
  using (Editor; EventStack; SimpleEditor; ViewStack; ViewStackMap;
    simple-editor)
open import Prover.Editor.Base
  using (BaseEditor; BaseEventStack; BaseViewStack; SimpleBaseEditor;
    base-editor-from-simple)
open import Prover.Editor.Child
  using (ChildEditor; SimpleChildEditor; child-editor-from-simple)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatViewStack)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

module _
  {K : Set}
  where

  module ViewStackParent
    (V : BaseViewStack)
    (V' : K → FlatViewStack)
    where

    open BaseViewStack V public
      using (View; ViewPath)

    ViewInner
      : (v : View)
      → ViewPath v
      → Set
    ViewInner _ _
      = k ∈ K × FlatViewStack.View (V' k)

    ViewInnerPath
      : (v : View)
      → (vp : ViewPath v)
      → ViewInner v vp
      → Set
    ViewInnerPath _ _ (k , v)
      = FlatViewStack.ViewPath (V' k) v

  view-stack-parent
    : BaseViewStack
    → (K → FlatViewStack)
    → ViewStack
  view-stack-parent V V'
    = record {ViewStackParent V V'}

-- ### EventStack

module _
  {K : Set}
  where

  module EventStackParent
    (E : BaseEventStack)
    (E' : K → FlatEventStack)
    where

    open BaseEventStack E public
      using (Mode)

    Event
      : Mode
      → Set
    Event m
      = BaseEventStack.Event E m ⊔ K

    ModeInner
      : Set
    ModeInner
      = k ∈ K × FlatEventStack.Mode (E' k)

    EventInner
      : ModeInner
      → Set
    EventInner (k , m)
      = FlatEventStack.Event (E' k) m

  event-stack-parent
    : BaseEventStack
    → (K → FlatEventStack)
    → EventStack
  event-stack-parent E E'
    = record {EventStackParent E E'}

-- ## Editors

-- ### Editor

module _
  {K : Set}
  {V : BaseViewStack}
  {E : BaseEventStack}
  {C : Category}
  where

  -- #### Module

  module EditorParent
    (V' : K → FlatViewStack)
    (E' : K → FlatEventStack)
    (e : BaseEditor V E C)
    (e' : (k : K) → ChildEditor (V' k) (E' k) e)
    where

    -- ##### Types

    open ViewStack (view-stack-parent V V')
    open EventStack (event-stack-parent E E')

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
      using (StatePath; initial; initial-path)

    StateInner
      : (s : State)
      → StatePath s
      → Set
    StateInner s sp
      = k ∈ K × FlatEditor.State (ChildEditor.flat-editor (e' k) s sp)

    StateInnerPath
      : (s : State)
      → (sp : StatePath s)
      → StateInner s sp
      → Set
    StateInnerPath s sp (k , s')
      = FlatEditor.StatePath (ChildEditor.flat-editor (e' k) s sp) s'

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

    -- ##### Draw
  
    open BaseEditor e public
      using (draw; draw-with; draw-path)

    draw-inner-with
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ViewInner
        (draw-with s sp)
        (draw-path s sp)
    draw-inner-with s sp (k , s') sp'
      = (k , FlatEditor.draw-with (ChildEditor.flat-editor (e' k) s sp) s' sp')

    draw-inner-path
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → ViewInnerPath
        (draw-with s sp)
        (draw-path s sp)
        (draw-inner-with s sp s' sp')
    draw-inner-path s sp (k , s') sp'
      = FlatEditor.draw-path (ChildEditor.flat-editor (e' k) s sp) s' sp'

    draw-stack
      : ViewStackMap StateStack (view-stack-parent V V')
    draw-stack
      = record
      { view
        = draw
      ; view-with
        = draw-with
      ; view-path
        = draw-path
      ; view-inner-with
        = draw-inner-with
      ; view-inner-path
        = draw-inner-path
      }

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode
      = BaseEditor.mode e

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner s sp (k , s') sp'
      = (k , FlatEditor.mode (ChildEditor.flat-editor (e' k) s sp) s' sp')

    -- ##### Handle
  
    open BaseEditor e public
      using (handle-direction; handle-direction-valid)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp (ι₁ e')
      = ι₁ (BaseEditor.handle e s sp e')
    handle s sp (ι₂ k)
      = ι₂ ((k , FlatEditor.initial (ChildEditor.flat-editor (e' k) s sp))
        , FlatEditor.initial-path (ChildEditor.flat-editor (e' k) s sp))

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
    handle-inner s sp (k , s') sp' e''
      with FlatEditor.handle (ChildEditor.flat-editor (e' k) s sp) s' sp' e''
    ... | (s'' , sp'')
      = ((k , s'') , sp'')

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape s sp (k , s') sp'
      with FlatEditor.handle-escape (ChildEditor.flat-editor (e' k) s sp) s' sp'
    ... | nothing
      = nothing
    ... | just (s'' , sp'')
      = just ((k , s'') , sp'')

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return s sp (k , s') sp'
      with FlatEditor.handle-return (ChildEditor.flat-editor (e' k) s sp) s' sp'
    ... | ι₁ x
      = ι₁ (ChildEditor.update (e' k) s sp x)
    ... | ι₂ (s'' , sp'')
      = ι₂ ((k , s'') , sp'')

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction s sp (k , s')
      = FlatEditor.handle-direction (ChildEditor.flat-editor (e' k) s sp) s'

  -- #### Function

  editor-parent
    : (V' : K → FlatViewStack)
    → (E' : K → FlatEventStack)
    → (e : BaseEditor V E C)
    → ((k : K) → ChildEditor (V' k) (E' k) e)
    → Editor
      (view-stack-parent V V')
      (event-stack-parent E E') C
  editor-parent V' E' e e'
    = record {EditorParent V' E' e e'}

-- ### SimpleEditor

simple-editor-parent
  : {K A : Set}
  → {V : BaseViewStack}
  → {E : BaseEventStack}
  → (V' : K → FlatViewStack)
  → (E' : K → FlatEventStack)
  → (e : SimpleBaseEditor V E A)
  → ((k : K) → SimpleChildEditor (V' k) (E' k) e)
  → SimpleEditor
    (view-stack-parent V V')
    (event-stack-parent E E') A
simple-editor-parent V' E' e e'
  = simple-editor
    (editor-parent V' E'
      (base-editor-from-simple e) 
      (λ k → child-editor-from-simple (e' k)))

