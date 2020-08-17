module Prover.Editor.Map where

open import Prover.Category
  using (Category)
open import Prover.Category.Split
  using (SplitFunctor; split-functor-compose)
open import Prover.Category.Split.Unit
  using (split-functor-unit)
open import Prover.Category.Unit
  using (category-unit)
open import Prover.Editor
  using (Editor; EventStack; EventStackMap; MainEditor; PartialEditor;
    SimpleEditor; SplitEditor; SplitMainEditor; ViewStack; ViewStackMap; any;
    view-stack-map-compose-with)
open import Prover.Editor.Flat
  using (FlatEditor; FlatEventStack; FlatEventStackMap; FlatViewStack;
    FlatViewStackMap; flat-view-stack-map-compose)
open import Prover.Function.Split
  using (SplitFunction; split-functor-base)
open import Prover.Function.Split.Compose
  using (split-function-compose)
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

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  simple-editor-map-view-with
    : (A → ViewStackMap V W)
    → SimpleEditor V E A
    → SimpleEditor W E A
  simple-editor-map-view-with F (any e)
    = any (editor-map-view-with F e)
  
  simple-editor-map-view
    : ViewStackMap V W
    → SimpleEditor V E A
    → SimpleEditor W E A
  simple-editor-map-view F
    = simple-editor-map-view-with (const F)

-- ### PartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {A : Set}
  where

  module PartialEditorMapViewWith
    (F : Bool → ViewStackMap V W)
    (e : PartialEditor V E A)
    where

    open PartialEditor e public
      hiding (simple-editor)

    simple-editor
      : SimpleEditor W E State
    simple-editor
      = simple-editor-map-view-with
        (λ s → F (PartialEditor.is-complete e s))
        (PartialEditor.simple-editor e)

  partial-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → PartialEditor V E A
    → PartialEditor W E A
  partial-editor-map-view-with F e
    = record {PartialEditorMapViewWith F e}

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

-- ### MainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S A : Set}
  where

  module MainEditorMapViewWith
    (F : Bool → ViewStackMap V W)
    (e : MainEditor V E S A)
    where

    open MainEditor e public
      hiding (simple-editor)

    simple-editor
      : SimpleEditor W E A
    simple-editor
      = simple-editor-map-view-with
        (λ s → F (MainEditor.is-complete e s))
        (MainEditor.simple-editor e)

  main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → MainEditor V E S A
    → MainEditor W E S A
  main-editor-map-view-with F e
    = record {MainEditorMapViewWith F e}

  main-editor-map-view
    : ViewStackMap V W
    → MainEditor V E S A
    → MainEditor W E S A
  main-editor-map-view F
    = main-editor-map-view-with (const F)

-- ### SplitMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C : Category}
  where

  module SplitMainEditorMapViewWith
    (F : Bool → ViewStackMap V W)
    (e : SplitMainEditor V E S P C)
    where

    open SplitMainEditor e public
      hiding (editor)

    editor
      : Editor W E StateCategory
    editor
      = editor-map-view-with
        (λ s → F (SplitMainEditor.is-complete e s))
        (SplitMainEditor.editor e)

  split-main-editor-map-view-with
    : (Bool → ViewStackMap V W)
    → SplitMainEditor V E S P C
    → SplitMainEditor W E S P C
  split-main-editor-map-view-with F e
    = record {SplitMainEditorMapViewWith F e}

  split-main-editor-map-view
    : ViewStackMap V W
    → SplitMainEditor V E S P C
    → SplitMainEditor W E S P C
  split-main-editor-map-view F
    = split-main-editor-map-view-with (const F)

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
simple-editor-map-event G (any e)
  = any (editor-map-event G e)

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
      hiding (simple-editor)

    simple-editor
      : SimpleEditor V F State
    simple-editor
      = simple-editor-map-event G
        (PartialEditor.simple-editor e)

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

-- ### MainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S A : Set}
  where

  module MainEditorMapEvent
    (G : EventStackMap E F)
    (e : MainEditor V E S A)
    where

    open MainEditor e public
      hiding (simple-editor)

    simple-editor
      : SimpleEditor V F A
    simple-editor
      = simple-editor-map-event G
        (MainEditor.simple-editor e)

  main-editor-map-event
    : EventStackMap E F
    → MainEditor V E S A
    → MainEditor V F S A
  main-editor-map-event G e
    = record {MainEditorMapEvent G e}

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S P : Set}
  {C : Category}
  where

  module SplitMainEditorMapEvent
    (G : EventStackMap E F)
    (e : SplitMainEditor V E S P C)
    where

    open SplitMainEditor e public
      hiding (editor)

    editor
      : Editor V F StateCategory
    editor
      = editor-map-event G
        (SplitMainEditor.editor e)

  split-main-editor-map-event
    : EventStackMap E F
    → SplitMainEditor V E S P C
    → SplitMainEditor V F S P C
  split-main-editor-map-event G e
    = record {SplitMainEditorMapEvent G e}

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

-- ## State

-- ### MainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S T A : Set}
  where

  module MainEditorMapState
    (F : SplitFunction T S)
    (e : MainEditor V E S A)
    where

    open MainEditor e public
      hiding (split-function)

    split-function
      : SplitFunction T A
    split-function
      = split-function-compose
        (MainEditor.split-function e) F

  main-editor-map-state
    : SplitFunction T S
    → MainEditor V E S A
    → MainEditor V E T A
  main-editor-map-state F e
    = record {MainEditorMapState F e}

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S T P : Set}
  {C : Category}
  where

  module SplitMainEditorMapState
    (F : SplitFunction T S)
    (e : SplitMainEditor V E S P C)
    where

    open SplitMainEditor e public
      hiding (state-split-function)

    state-split-function
      : SplitFunction T State
    state-split-function
      = split-function-compose
        (SplitMainEditor.state-split-function e) F

  split-main-editor-map-state
    : SplitFunction T S
    → SplitMainEditor V E S P C
    → SplitMainEditor V E T P C
  split-main-editor-map-state F e
    = record {SplitMainEditorMapState F e}

-- ## Pure

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P Q : Set}
  {C : Category}
  where

  module SplitMainEditorMapPure
    (F : SplitFunction Q P)
    (e : SplitMainEditor V E S P C)
    where

    open SplitMainEditor e public
      hiding (pure-split-function)

    pure-split-function
      : SplitFunction Q (Category.Object C)
    pure-split-function
      = split-function-compose
        (SplitMainEditor.pure-split-function e) F

  split-main-editor-map-pure
    : SplitFunction Q P
    → SplitMainEditor V E S P C
    → SplitMainEditor V E S Q C
  split-main-editor-map-pure F e
    = record {SplitMainEditorMapPure F e}

-- ## Result

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
  → SplitFunction A B
  → SplitEditor V E (category-unit A)
  → SplitEditor V E (category-unit B)
split-editor-map-simple F
  = split-editor-map (split-functor-unit F)

-- ### SplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {C D : Category}
  where

  module SplitMainEditorMap
    (F : SplitFunctor C D)
    (e : SplitMainEditor V E S P C)
    where

    open SplitMainEditor e public
      hiding (split-functor; pure-split-function)

    split-functor
      : SplitFunctor StateCategory D
    split-functor
      = split-functor-compose F
        (SplitMainEditor.split-functor e)

    pure-split-function
      : SplitFunction P (Category.Object D)
    pure-split-function
      = split-function-compose
        (split-functor-base F)
        (SplitMainEditor.pure-split-function e)

  split-main-editor-map
    : SplitFunctor C D
    → SplitMainEditor V E S P C
    → SplitMainEditor V E S P D
  split-main-editor-map F e
    = record {SplitMainEditorMap F e}

split-main-editor-map-simple
  : {V : ViewStack}
  → {E : EventStack}
  → {S P : Set}
  → {A B : Set}
  → SplitFunction A B
  → SplitMainEditor V E S P (category-unit A)
  → SplitMainEditor V E S P (category-unit B)
split-main-editor-map-simple F
  = split-main-editor-map (split-functor-unit F)

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
      → StatePath s
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

