module Prover.Editor.Flatten where

open import Prover.Category
  using (Category)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Editor
  using (Editor; EventStack; SimpleEditor; SimpleMainEditor;
    SimplePartialEditor; SimpleSplitEditor; SplitEditor; ViewStack;
    ViewStackMap)
open import Prover.Editor.Base
  using (BaseEventStack; BaseViewStack)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap; FlatMainEditor;
    FlatViewStack; FlatViewStackMap)
open import Prover.Editor.Lift
  using (event-stack-lift; view-stack-lift)
open import Prover.Editor.Map
  using (flat-editor-map)
open import Prover.Editor.Unit
  using (editor-unit)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

module ViewStackFlatten
  (V : ViewStack)
  where

  View
    : Set
  View
    = v ∈ ViewStack.View V
    × Maybe (Σ (ViewStack.ViewPath V v) (ViewStack.ViewInner V v))

  ViewPath
    : View
    → Set
  ViewPath (v , nothing)
    = ViewStack.ViewPath V v
  ViewPath (v , just (vp , v'))
    = ViewStack.ViewInnerPath V v vp v'

view-stack-flatten
  : ViewStack
  → FlatViewStack
view-stack-flatten V
  = record {ViewStackFlatten V}

-- ### EventStack

module EventStackFlatten
  (E : EventStack)
  where

  Mode
    : Set
  Mode
    = EventStack.Mode E
    ⊔ EventStack.ModeInner E

  Event
    : Mode
    → Set
  Event (ι₁ m)
    = EventStack.Event E m
  Event (ι₂ m)
    = EventStack.EventInner E m

event-stack-flatten
  : EventStack
  → FlatEventStack
event-stack-flatten E
  = record {EventStackFlatten E}

-- ### BaseViewStack

-- #### Flatten

base-view-stack-flatten
  : BaseViewStack
  → FlatViewStack
base-view-stack-flatten V
  = record {BaseViewStack V}

-- #### Conversion

module BaseViewStackFlattenLift
  (V : BaseViewStack)
  where

  view-with
    : (v : FlatViewStack.View (view-stack-flatten (view-stack-lift V)))
    → FlatViewStack.ViewPath (view-stack-flatten (view-stack-lift V)) v
    → FlatViewStack.View (base-view-stack-flatten V)
  view-with (v , nothing) _
    = v
  
  view-path
    : (v : FlatViewStack.View (view-stack-flatten (view-stack-lift V)))
    → (vp : FlatViewStack.ViewPath (view-stack-flatten (view-stack-lift V)) v)
    → FlatViewStack.ViewPath (base-view-stack-flatten V) (view-with v vp)
  view-path (_ , nothing) vp
    = vp

base-view-stack-flatten-lift
  : (V : BaseViewStack)
  → FlatViewStackMap
    (view-stack-flatten (view-stack-lift V))
    (base-view-stack-flatten V)
base-view-stack-flatten-lift V
  = record {BaseViewStackFlattenLift V}

-- ### BaseEventStack

-- #### Flatten

base-event-stack-flatten
  : BaseEventStack
  → FlatEventStack
base-event-stack-flatten E
  = record {BaseEventStack E}

-- #### Conversion

module BaseEventStackFlattenLift
  (E : BaseEventStack)
  where

  mode
    : FlatEventStack.Mode (event-stack-flatten (event-stack-lift E))
    → FlatEventStack.Mode (base-event-stack-flatten E)
  mode (ι₁ e)
    = e

  event
    : (m : FlatEventStack.Mode (event-stack-flatten (event-stack-lift E)))
    → FlatEventStack.Event (base-event-stack-flatten E) (mode m)
    → FlatEventStack.Event (event-stack-flatten (event-stack-lift E)) m
  event (ι₁ _)
    = id

base-event-stack-flatten-lift
  : (E : BaseEventStack)
  → FlatEventStackMap
    (event-stack-flatten (event-stack-lift E))
    (base-event-stack-flatten E)
base-event-stack-flatten-lift E
  = record {BaseEventStackFlattenLift E}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V W : ViewStack}
  where

  module ViewStackMapFlatten
    (F : ViewStackMap V W)
    where

    view-with
      : (v : FlatViewStack.View (view-stack-flatten V))
      → FlatViewStack.ViewPath (view-stack-flatten V) v
      → FlatViewStack.View (view-stack-flatten W)
    view-with (v , nothing) vp
      = (ViewStackMap.view-with F v vp , nothing)
    view-with (v , just (vp , v')) vp'
      = (ViewStackMap.view-with F v vp
        , just (ViewStackMap.view-path F v vp
          , ViewStackMap.view-inner-with F v vp v' vp'))

    view-path
      : (v : FlatViewStack.View (view-stack-flatten V))
      → (vp : FlatViewStack.ViewPath (view-stack-flatten V) v)
      → FlatViewStack.ViewPath (view-stack-flatten W) (view-with v vp)
    view-path (v , nothing)
      = ViewStackMap.view-path F v
    view-path (v , just (vp , v'))
      = ViewStackMap.view-inner-path F v vp v'

  view-stack-map-flatten
    : ViewStackMap V W
    → FlatViewStackMap
      (view-stack-flatten V)
      (view-stack-flatten W)
  view-stack-map-flatten F
    = record {ViewStackMapFlatten F}

-- ## Editors (basic)

-- ### Editor

module _
  {V : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  -- #### Module

  module EditorFlatten
    (e : Editor V E C)
    where

    -- ##### Types

    open FlatEventStack (event-stack-flatten E)

    -- ##### State
  
    StateStack
      : FlatViewStack
    StateStack
      = view-stack-flatten
        (Editor.StateStack e)
  
    open FlatViewStack StateStack public using () renaming
      ( View
        to State
      ; ViewPath
        to StatePath
      )
  
    initial
      : State
    initial
      = (Editor.initial e , nothing)
  
    initial-path
      : StatePath initial
    initial-path
      = Editor.initial-path' e

    -- ##### Draw

    draw-stack
      : FlatViewStackMap StateStack (view-stack-flatten V)
    draw-stack
      = view-stack-map-flatten
        (Editor.draw-stack e)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (s , nothing) sp
      = ι₁ (Editor.mode e s sp)
    mode (s , just (sp , s')) sp'
      = ι₂ (Editor.mode-inner e s sp s' sp')

    -- ##### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath
    handle (s , nothing) sp e'
      with Editor.handle e s sp e'
    ... | ι₁ (s' , sp' , _)
      = ((s' , nothing) , sp')
    ... | ι₂ (s' , sp')
      = ((s , just (sp , s')) , sp')
    handle (s , just (sp , s')) sp' e'
      with Editor.handle-inner e s sp s' sp' e'
    ... | (s'' , sp'')
      = ((s , just (sp , s'')) , sp'')

    handle-escape
      : (s : State)
      → StatePath s
      → Maybe (Σ State StatePath)
    handle-escape (s , nothing) sp
      with Editor.handle-escape e s sp
    ... | nothing
      = nothing
    ... | just (ι₁ (s' , sp' , _))
      = just ((s' , nothing) , sp')
    ... | just (ι₂ (s' , sp'))
      = just ((s , just (sp , s')) , sp')
    handle-escape (s , just (sp , s')) sp'
      with Editor.handle-inner-escape e s sp s' sp'
    ... | nothing
      = just ((s , nothing) , sp)
    ... | just (s'' , sp'')
      = just ((s , just (sp , s'')) , sp'')

    handle-return
      : (s : State)
      → StatePath s
      → Category.Object C ⊔ Σ State StatePath
    handle-return (s , nothing) sp
      with Editor.handle-return e s sp
    ... | nothing
      = ι₁ s
    ... | just (ι₁ (s' , sp' , _))
      = ι₂ ((s' , nothing) , sp')
    ... | just (ι₂ (s' , sp'))
      = ι₂ ((s , just (sp , s')) , sp')
    handle-return (s , just (sp , s')) sp'
      with Editor.handle-inner-return e s sp s' sp'
    ... | ι₁ (s'' , sp'' , _)
      = ι₂ ((s'' , nothing) , sp'')
    ... | ι₂ (s'' , sp'')
      = ι₂ ((s , just (sp , s'')) , sp'')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → StatePath s
    handle-direction (s , nothing) sp d
      = maybe (Editor.handle-direction e s sp d) sp id
    handle-direction (s , just (sp , s')) sp' d
      = Editor.handle-inner-direction e s sp s' sp' d

  -- #### Function

  editor-flatten
    : Editor V E C
    → FlatEditor
      (view-stack-flatten V)
      (event-stack-flatten E)
      (Category.Object C)
  editor-flatten e
    = record {EditorFlatten e}

-- ### SimpleEditor 

simple-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-editor-flatten
  = editor-flatten
  ∘ editor-unit

-- ## Editors (nondependent)

-- ### SplitEditor

split-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {C : Category}
  → SplitEditor V E C
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E)
    (Category.Object C)
split-editor-flatten e
  = flat-editor-map (SplitEditor.base e)
  $ editor-flatten (SplitEditor.editor e)

-- ### SimplePartialEditor

simple-partial-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimplePartialEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-partial-editor-flatten e
  = flat-editor-map (SimplePartialEditor.base e)
  $ simple-editor-flatten (SimplePartialEditor.editor e)

-- ### SimpleSplitEditor

simple-split-editor-flatten
  : {V : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → SimpleSplitEditor V E A
  → FlatEditor
    (view-stack-flatten V)
    (event-stack-flatten E) A
simple-split-editor-flatten e
  = flat-editor-map (SimpleSplitEditor.base e)
  $ simple-editor-flatten (SimpleSplitEditor.editor e)

-- ### SimpleMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  where

  module SimpleMainEditorFlatten
    (e : SimpleMainEditor V E S)
    where

    editor
      : Editor V E
        (category-unit (SimpleMainEditor.State e))
    editor
      = editor-unit
        (SimpleMainEditor.editor e)

    flat-editor
      : FlatEditor
        (view-stack-flatten V)
        (event-stack-flatten E)
        (SimpleMainEditor.State e)
    flat-editor
      = editor-flatten editor

    open FlatEditor flat-editor public
      hiding (handle-escape; handle-return)

    initial-with
      : S
      → State
    initial-with s
      with SimpleMainEditor.state-decode e s
    ... | nothing
      = initial
    ... | just s'
      = (s' , nothing)

    initial-path-with
      : (s : S)
      → StatePath (initial-with s)
    initial-path-with s
      with SimpleMainEditor.state-decode e s
    ... | nothing
      = initial-path
    ... | just s'
      = Editor.initial-path editor s'

    handle-escape
      : (s : State)
      → StatePath s
      → Σ State StatePath
    handle-escape s sp
      with FlatEditor.handle-escape flat-editor s sp
    ... | nothing
      = (s , sp)
    ... | just s'
      = s'

    handle-return
      : (s : State)
      → StatePath s
      → Σ State StatePath
    handle-return s sp
      with FlatEditor.handle-return flat-editor s sp
    ... | ι₁ _
      = (s , sp)
    ... | ι₂ s'
      = s'

    handle-save
      : State
      → S
    handle-save (s , _)
      = SimpleMainEditor.state-encode e s

  simple-main-editor-flatten
    : SimpleMainEditor V E S
    → FlatMainEditor
      (view-stack-flatten V)
      (event-stack-flatten E) S
  simple-main-editor-flatten e
    = record {SimpleMainEditorFlatten e}

