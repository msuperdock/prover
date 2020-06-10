module Prover.Editor.Map where

open import Prover.Category
  using (Category)
open import Prover.Category.Simple
  using (PartialFunction)
open import Prover.Category.Split
  using (SplitFunctor; split-functor-compose)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Editor
  using (Editor; EventStack; EventStackMap; PartialEditor; SimpleEditor;
    SplitEditor; ViewStack; ViewStackMap; partial-editor; simple-editor;
    view-stack-map-compose-with)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap; FlatViewStack;
    FlatViewStackMap; flat-view-stack-map-compose)
open import Prover.Prelude

-- ## View

-- ### Editor

module _
  {V W : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  module EditorMapViewWith
    (F : Category.Object C → ViewStackMap V W)
    (e : Editor V E C)
    where

    open Editor e public
      hiding (draw-stack)

    draw-stack
      : ViewStackMap StateStack W
    draw-stack
      = view-stack-map-compose-with F
        (Editor.draw-stack e)

  editor-map-view-with
    : (Category.Object C → ViewStackMap V W)
    → Editor V E C
    → Editor W E C
  editor-map-view-with F e
    = record {EditorMapViewWith F e}

  editor-map-view
    : ViewStackMap V W
    → Editor V E C
    → Editor W E C
  editor-map-view F
    = editor-map-view-with (const F)

-- ### SimpleEditor

simple-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {A : Set}
  → ViewStackMap V W
  → SimpleEditor V E A
  → SimpleEditor W E A
simple-editor-map-view F (simple-editor e)
  = simple-editor (editor-map-view F e)

-- ### PartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  module PartialEditorMapView
    (F : Bool → ViewStackMap V W)
    (e : PartialEditor V E A)
    where

    open PartialEditor e public
      hiding (editor)

    editor
      : Editor W E StateCategory
    editor
      = editor-map-view-with
        (λ s → F (PartialEditor.is-complete e s))
        (PartialEditor.editor e)

  partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → PartialEditor V E A
    → PartialEditor W E A
  partial-editor-map-view-with F e
    = record {PartialEditorMapView F e}

  partial-editor-map-view
    : ViewStackMap V W
    → PartialEditor V E A
    → PartialEditor W E A
  partial-editor-map-view F
    = partial-editor-map-view-with (const F)

-- ### SplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {C : Category}
  where

  module SplitEditorMapViewWith
    (F : Bool → ViewStackMap V W)
    (e : SplitEditor V E C)
    where

    open SplitEditor e public
      hiding (editor)

    editor
      : Editor W E StateCategory
    editor
      = editor-map-view-with
        (λ s → F (SplitEditor.is-complete e s))
        (SplitEditor.editor e)

  split-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view-with F e
    = record {SplitEditorMapViewWith F e}

  split-editor-map-view
    : ViewStackMap V W
    → SplitEditor V E C
    → SplitEditor W E C
  split-editor-map-view F
    = split-editor-map-view-with (const F)

-- ### FlatEditor

module _
  {V W : FlatViewStack}
  {E : FlatEventStack}
  {A : Set}
  where

  module FlatEditorMapView
    (F : FlatViewStackMap V W)
    (e : FlatEditor V E A)
    where

    open FlatEditor e public
      hiding (draw-stack)

    draw-stack
      : FlatViewStackMap StateStack W
    draw-stack
      = flat-view-stack-map-compose F
        (FlatEditor.draw-stack e)

  flat-editor-map-view
    : FlatViewStackMap V W
    → FlatEditor V E A
    → FlatEditor W E A
  flat-editor-map-view F e
    = record {FlatEditorMapView F e}

-- ## Event

-- ### Editor

module _
  {V : ViewStack}
  {E F : EventStack}
  {C : Category}
  where

  module EditorMapEvent
    (G : EventStackMap E F)
    (e : Editor V E C)
    where

    open EventStack F

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

    open Editor e public
      hiding (mode; mode-inner; handle; handle-inner)

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode s sp
      = EventStackMap.mode G
        (Editor.mode e s sp)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner s sp s' sp'
      = EventStackMap.mode-inner G
        (Editor.mode-inner e s sp s' sp')

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle s sp e'
      = Editor.handle e s sp
        (EventStackMap.event G (Editor.mode e s sp) e')

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner s sp s' sp' e'
      = Editor.handle-inner e s sp s' sp'
        (EventStackMap.event-inner G (Editor.mode-inner e s sp s' sp') e')

  editor-map-event
    : EventStackMap E F
    → Editor V E C
    → Editor V F C
  editor-map-event G e
    = record {EditorMapEvent G e}

-- ### SimpleEditor

simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {A : Set}
  → EventStackMap E F
  → SimpleEditor V E A
  → SimpleEditor V F A
simple-editor-map-event G (simple-editor e)
  = simple-editor (editor-map-event G e)

-- ### PartialEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {A : Set}
  where

  module PartialEditorMapEvent
    (G : EventStackMap E F)
    (e : PartialEditor V E A)
    where

    open PartialEditor e public
      hiding (editor)

    editor
      : Editor V F StateCategory
    editor
      = editor-map-event G
        (PartialEditor.editor e)

  partial-editor-map-event
    : EventStackMap E F
    → PartialEditor V E A
    → PartialEditor V F A
  partial-editor-map-event G e
    = record {PartialEditorMapEvent G e}

-- ### SplitEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {C : Category}
  where

  module SplitEditorMapEvent
    (G : EventStackMap E F)
    (e : SplitEditor V E C)
    where

    open SplitEditor e public
      hiding (editor)

    editor
      : Editor V F StateCategory
    editor
      = editor-map-event G
        (SplitEditor.editor e)

  split-editor-map-event
    : EventStackMap E F
    → SplitEditor V E C
    → SplitEditor V F C
  split-editor-map-event G e
    = record {SplitEditorMapEvent G e}

-- ### FlatEditor

module _
  {V : FlatViewStack}
  {E F : FlatEventStack}
  {A : Set}
  where

  module FlatEditorMapEvent
    (G : FlatEventStackMap E F)
    (e : FlatEditor V E A)
    where

    open FlatEventStack F

    open FlatEditor e public
      hiding (mode; handle)
    
    mode
      : (s : State)
      → StatePath s
      → Mode
    mode s sp
      = FlatEventStackMap.mode G
        (FlatEditor.mode e s sp)

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → Σ State StatePath
    handle s sp e'
      = FlatEditor.handle e s sp
        (FlatEventStackMap.event G (FlatEditor.mode e s sp) e')

  flat-editor-map-event
    : FlatEventStackMap E F
    → FlatEditor V E A
    → FlatEditor V F A
  flat-editor-map-event G e
    = record {FlatEditorMapEvent G e}

-- ## Result

-- ### SimpleEditor

simple-editor-map
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → PartialFunction A B
  → SimpleEditor V E A
  → PartialEditor V E B
simple-editor-map f (simple-editor e)
  = partial-editor e f

-- ### PartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {A B : Set}
  where

  module PartialEditorMap
    (f : A → Maybe B)
    (e : PartialEditor V E A)
    where

    open PartialEditor e public
      hiding (base)

    base
      : State
      → Maybe B
    base s
      with PartialEditor.base e s
    ... | nothing
      = nothing
    ... | just x
      = f x

  partial-editor-map
    : (A → Maybe B)
    → PartialEditor V E A
    → PartialEditor V E B
  partial-editor-map f e
    = record {PartialEditorMap f e}

-- ### SplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {C D : Category}
  where

  module SplitEditorMap
    (F : SplitFunctor C D)
    (e : SplitEditor V E C)
    where

    open SplitEditor e public
      hiding (split-functor)

    split-functor
      : SplitFunctor StateCategory D
    split-functor
      = split-functor-compose F
        (SplitEditor.split-functor e)

  split-editor-map
    : SplitFunctor C D
    → SplitEditor V E C
    → SplitEditor V E D
  split-editor-map F e
    = record {SplitEditorMap F e}

split-editor-map-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {A B : Set}
  → PartialRetraction A B
  → SplitEditor V E (category-unit A)
  → SplitEditor V E (category-unit B)
split-editor-map-simple F
  = split-editor-map (split-functor-unit F)

-- ### FlatEditor

module _
  {V : FlatViewStack}
  {E : FlatEventStack}
  {A B : Set}
  where

  module FlatEditorMap
    (f : A → Maybe B)
    (e : FlatEditor V E A)
    where

    open FlatEditor e public
      hiding (handle-return)

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → B ⊔ Σ State StatePath
    handle-return s sp
      with FlatEditor.handle-return e s sp
    ... | ι₂ s'
      = ι₂ s'
    ... | ι₁ x
      with f x
    ... | nothing
      = ι₂ (s , sp)
    ... | just y
      = ι₁ y

  flat-editor-map
    : (A → Maybe B)
    → FlatEditor V E A
    → FlatEditor V E B
  flat-editor-map f e
    = record {FlatEditorMap f e}

