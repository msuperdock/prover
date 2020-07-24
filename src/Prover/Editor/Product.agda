module Prover.Editor.Product where

open import Prover.Category
  using (Category)
open import Prover.Category.Product
  using (category-product)
open import Prover.Category.Split
  using (SplitFunctor)
open import Prover.Category.Split.Product
  using (split-functor-product)
open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Category.Split.Base.Product
  using (split-function-product)
open import Prover.Editor
  using (Editor; EventStack; PartialEditor; MainEditor; SimpleEditor;
    SplitEditor; SplitMainEditor; ViewStack; ViewStackMap; any)
open import Prover.Prelude

-- ## Stacks

-- ### ViewStack

module ViewStackProduct
  (V₁ V₂ : ViewStack)
  where

  View
    : Set
  View
    = ViewStack.View V₁
    × ViewStack.View V₂

  ViewPath
    : View
    → Set
  ViewPath (v₁ , v₂)
    = ViewStack.ViewPath V₁ v₁
    ⊔ ViewStack.ViewPath V₂ v₂
  
  ViewInner
    : (v : View)
    → ViewPath v
    → Set
  ViewInner (v₁ , _) (ι₁ vp₁)
    = ViewStack.ViewInner V₁ v₁ vp₁
  ViewInner (_ , v₂) (ι₂ vp₂)
    = ViewStack.ViewInner V₂ v₂ vp₂

  ViewInnerPath
    : (v : View)
    → (vp : ViewPath v)
    → ViewInner v vp
    → Set
  ViewInnerPath (v₁ , _) (ι₁ vp₁)
    = ViewStack.ViewInnerPath V₁ v₁ vp₁
  ViewInnerPath (_ , v₂) (ι₂ vp₂)
    = ViewStack.ViewInnerPath V₂ v₂ vp₂

view-stack-product
  : ViewStack
  → ViewStack
  → ViewStack
view-stack-product V₁ V₂
  = record {ViewStackProduct V₁ V₂}

-- ### EventStack

module EventStackProduct
  (E₁ E₂ : EventStack)
  where

  Mode
    : Set
  Mode
    = EventStack.Mode E₁
    ⊔ EventStack.Mode E₂

  ModeInner
    : Set
  ModeInner
    = EventStack.ModeInner E₁
    ⊔ EventStack.ModeInner E₂

  Event
    : Mode
    → Set
  Event (ι₁ m₁)
    = EventStack.Event E₁ m₁
  Event (ι₂ m₂)
    = EventStack.Event E₂ m₂

  EventInner
    : ModeInner
    → Set
  EventInner (ι₁ m₁)
    = EventStack.EventInner E₁ m₁
  EventInner (ι₂ m₂)
    = EventStack.EventInner E₂ m₂

event-stack-product
  : EventStack
  → EventStack
  → EventStack
event-stack-product E₁ E₂
  = record {EventStackProduct E₁ E₂}

-- ## StackMaps

-- ### ViewStackMap

module _
  {V₁ V₂ W₁ W₂ : ViewStack}
  where

  module ViewStackMapProduct
    (F₁ : ViewStackMap V₁ W₁)
    (F₂ : ViewStackMap V₂ W₂)
    where

    view
      : ViewStack.View (view-stack-product V₁ V₂)
      → ViewStack.View (view-stack-product W₁ W₂)
    view (v₁ , v₂)
      = ViewStackMap.view F₁ v₁
      , ViewStackMap.view F₂ v₂

    view-with
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → ViewStack.ViewPath (view-stack-product V₁ V₂) v
      → ViewStack.View (view-stack-product W₁ W₂)
    view-with (v₁ , v₂) (ι₁ vp₁)
      = ViewStackMap.view-with F₁ v₁ vp₁
      , ViewStackMap.view F₂ v₂
    view-with (v₁ , v₂) (ι₂ vp₂)
      = ViewStackMap.view F₁ v₁
      , ViewStackMap.view-with F₂ v₂ vp₂
    
    view-path
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → ViewStack.ViewPath (view-stack-product W₁ W₂)
        (view-with v vp)
    view-path (v₁ , _) (ι₁ vp₁)
      = ι₁ (ViewStackMap.view-path F₁ v₁ vp₁)
    view-path (_ , v₂) (ι₂ vp₂)
      = ι₂ (ViewStackMap.view-path F₂ v₂ vp₂)

    view-inner-with
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → (v' : ViewStack.ViewInner (view-stack-product V₁ V₂) v vp)
      → ViewStack.ViewInnerPath (view-stack-product V₁ V₂) v vp v'
      → ViewStack.ViewInner (view-stack-product W₁ W₂)
        (view-with v vp)
        (view-path v vp)
    view-inner-with (v₁ , _) (ι₁ vp₁)
      = ViewStackMap.view-inner-with F₁ v₁ vp₁
    view-inner-with (_ , v₂) (ι₂ vp₂)
      = ViewStackMap.view-inner-with F₂ v₂ vp₂

    view-inner-path
      : (v : ViewStack.View (view-stack-product V₁ V₂))
      → (vp : ViewStack.ViewPath (view-stack-product V₁ V₂) v)
      → (v' : ViewStack.ViewInner (view-stack-product V₁ V₂) v vp)
      → (vp' : ViewStack.ViewInnerPath (view-stack-product V₁ V₂) v vp v')
      → ViewStack.ViewInnerPath (view-stack-product W₁ W₂)
        (view-with v vp)
        (view-path v vp)
        (view-inner-with v vp v' vp')
    view-inner-path (v₁ , _) (ι₁ vp₁)
      = ViewStackMap.view-inner-path F₁ v₁ vp₁
    view-inner-path (_ , v₂) (ι₂ vp₂)
      = ViewStackMap.view-inner-path F₂ v₂ vp₂

  view-stack-map-product
    : ViewStackMap V₁ W₁
    → ViewStackMap V₂ W₂
    → ViewStackMap
      (view-stack-product V₁ V₂)
      (view-stack-product W₁ W₂)
  view-stack-map-product F₁ F₂
    = record {ViewStackMapProduct F₁ F₂}

-- ## Editors

-- ### Editor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {C₁ C₂ : Category}
  where

  -- #### Module

  module EditorProduct
    (d : Direction)
    (e₁ : Editor V₁ E₁ C₁)
    (e₂ : Editor V₂ E₂ C₂)
    where

    -- ##### Types

    open EventStack (event-stack-product E₁ E₂)

    open Category (category-product C₁ C₂) using () renaming
      ( Object
        to State
      ; Arrow
        to StateArrow
      )

    -- ##### State

    StateStack
      : ViewStack
    StateStack
      = view-stack-product
        (Editor.StateStack e₁)
        (Editor.StateStack e₂)

    open ViewStack StateStack public using () renaming
      ( ViewPath
        to StatePath
      ; ViewInner
        to StateInner
      ; ViewInnerPath
        to StateInnerPath
      )

    initial
      : State
    initial
      = Editor.initial e₁
      , Editor.initial e₂

    initial-path
      : (s : State)
      → StatePath s
    initial-path (s₁ , _)
      = ι₁ (Editor.initial-path e₁ s₁)

    initial-path-with
      : (s : State)
      → Direction
      → StatePath s
    initial-path-with (s₁ , s₂) d'
      with d' ≟ d dir
    ... | no _
      = ι₁ (Editor.initial-path-with e₁ s₁ d')
    ... | yes _
      = ι₂ (Editor.initial-path-with e₂ s₂ d')

    -- ##### Draw

    draw-stack
      : ViewStackMap StateStack (view-stack-product V₁ V₂)
    draw-stack
      = view-stack-map-product
        (Editor.draw-stack e₁)
        (Editor.draw-stack e₂)

    -- ##### Mode

    mode
      : (s : State)
      → StatePath s
      → Mode
    mode (s₁ , _) (ι₁ sp₁)
      = ι₁ (Editor.mode e₁ s₁ sp₁)
    mode (_ , s₂) (ι₂ sp₂)
      = ι₂ (Editor.mode e₂ s₂ sp₂)

    mode-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → ModeInner
    mode-inner (s₁ , _) (ι₁ sp₁) s₁' sp₁'
      = ι₁ (Editor.mode-inner e₁ s₁ sp₁ s₁' sp₁')
    mode-inner (_ , s₂) (ι₂ sp₂) s₂' sp₂'
      = ι₂ (Editor.mode-inner e₂ s₂ sp₂ s₂' sp₂')

    -- ##### Handle

    handle
      : (s : State)
      → (sp : StatePath s)
      → Event (mode s sp)
      → (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle (s₁ , s₂) (ι₁ sp₁) e₁'
      with Editor.handle e₁ s₁ sp₁ e₁'
    ... | ι₁ (s₁' , sp₁' , f₁)
      = ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , Category.identity C₂ s₂))
    ... | ι₂ s₁'
      = ι₂ s₁'
    handle (s₁ , s₂) (ι₂ sp₂) e₂'
      with Editor.handle e₂ s₂ sp₂ e₂'
    ... | ι₁ (s₂' , sp₂' , f₂)
      = ι₁ ((s₁ , s₂') , ι₂ sp₂' , (Category.identity C₁ s₁ , f₂))
    ... | ι₂ s₂'
      = ι₂ s₂'

    handle-escape
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-escape (s₁ , s₂) (ι₁ sp₁)
      with Editor.handle-escape e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , Category.identity C₂ s₂)))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-escape (s₁ , s₂) (ι₂ sp₂)
      with Editor.handle-escape e₂ s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ ((s₁ , s₂') , ι₂ sp₂' , (Category.identity C₁ s₁ , f₂)))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-return
      : (s : State)
      → (sp : StatePath s)
      → Maybe (s' ∈ State × sp' ∈ StatePath s' × StateArrow s s'
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp))
    handle-return (s₁ , s₂) (ι₁ sp₁)
      with Editor.handle-return e₁ s₁ sp₁
    ... | nothing
      = nothing
    ... | just (ι₁ (s₁' , sp₁' , f₁))
      = just (ι₁ ((s₁' , s₂) , ι₁ sp₁' , (f₁ , Category.identity C₂ s₂)))
    ... | just (ι₂ s₁')
      = just (ι₂ s₁')
    handle-return (s₁ , s₂) (ι₂ sp₂)
      with Editor.handle-return e₂ s₂ sp₂
    ... | nothing
      = nothing
    ... | just (ι₁ (s₂' , sp₂' , f₂))
      = just (ι₁ ((s₁ , s₂') , ι₂ sp₂' , (Category.identity C₁ s₁ , f₂)))
    ... | just (ι₂ s₂')
      = just (ι₂ s₂')

    handle-direction
      : (s : State)
      → StatePath s
      → Direction
      → Maybe (StatePath s)
    handle-direction (s₁ , s₂) (ι₁ sp₁) d'
      with Editor.handle-direction e₁ s₁ sp₁ d'
      | d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₂ (Editor.initial-path-with e₂ s₂ (Direction.reverse d')))
    ... | just sp₁' | _
      = just (ι₁ sp₁')
    handle-direction (s₁ , s₂) (ι₂ sp₂) d'
      with Editor.handle-direction e₂ s₂ sp₂ d'
      | Direction.reverse d' ≟ d dir
    ... | nothing | no _
      = nothing
    ... | nothing | yes _
      = just (ι₁ (Editor.initial-path-with e₁ s₁ (Direction.reverse d')))
    ... | just sp₂' | _
      = just (ι₂ sp₂')

    handle-direction-valid
      : (s : State)
      → (d' : Direction)
      → handle-direction s (initial-path-with s d') d' ≡ nothing
    handle-direction-valid _ d'
      with d' ≟ d dir
      | inspect (_≟_dir d') d
    handle-direction-valid (s₁ , _) d' | no _ | [ _ ]
      with Editor.handle-direction e₁ s₁ (Editor.initial-path-with e₁ s₁ d') d'
      | Editor.handle-direction-valid e₁ s₁ d'
      | d' ≟ d dir
    handle-direction-valid _ _ _ | _ | [ refl ] | _ | refl | _
      = refl
    handle-direction-valid (_ , s₂) d' | yes refl | _
      with Editor.handle-direction e₂ s₂ (Editor.initial-path-with e₂ s₂ d') d'
      | Editor.handle-direction-valid e₂ s₂ d'
      | Direction.reverse d' ≟ d dir
    ... | _ | refl | no _
      = refl
    ... | _ | _ | yes p
      = ⊥-elim (Direction.reverse-≢ d' p)

    handle-inner
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → (sp' : StateInnerPath s sp s')
      → EventInner (mode-inner s sp s' sp')
      → Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner e₁ s₁ sp₁
    handle-inner (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner e₂ s₂ sp₂

    handle-inner-escape
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Maybe (Σ (StateInner s sp) (StateInnerPath s sp))
    handle-inner-escape (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner-escape e₁ s₁ sp₁
    handle-inner-escape (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner-escape e₂ s₂ sp₂

    handle-inner-return
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → (s'' ∈ State × sp'' ∈ StatePath s'' × StateArrow s s'')
        ⊔ Σ (StateInner s sp) (StateInnerPath s sp)
    handle-inner-return (s₁ , s₂) (ι₁ sp₁) s₁' sp₁'
      with Editor.handle-inner-return e₁ s₁ sp₁ s₁' sp₁'
    ... | ι₁ (s₁'' , sp₁'' , f₁)
      = ι₁ ((s₁'' , s₂) , ι₁ sp₁'' , (f₁ , Category.identity C₂ s₂))
    ... | ι₂ s₁''
      = ι₂ s₁''
    handle-inner-return (s₁ , s₂) (ι₂ sp₂) s₂' sp₂'
      with Editor.handle-inner-return e₂ s₂ sp₂ s₂' sp₂'
    ... | ι₁ (s₂'' , sp₂'' , f₂)
      = ι₁ ((s₁ , s₂'') , ι₂ sp₂'' , (Category.identity C₁ s₁ , f₂))
    ... | ι₂ s₂''
      = ι₂ s₂''

    handle-inner-direction
      : (s : State)
      → (sp : StatePath s)
      → (s' : StateInner s sp)
      → StateInnerPath s sp s'
      → Direction
      → StateInnerPath s sp s'
    handle-inner-direction (s₁ , _) (ι₁ sp₁)
      = Editor.handle-inner-direction e₁ s₁ sp₁
    handle-inner-direction (_ , s₂) (ι₂ sp₂)
      = Editor.handle-inner-direction e₂ s₂ sp₂

  -- #### Function

  -- Takes direction from first to second component.
  editor-product
    : Direction
    → Editor V₁ E₁ C₁
    → Editor V₂ E₂ C₂
    → Editor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (category-product C₁ C₂)
  editor-product d e₁ e₂
    = record {EditorProduct d e₁ e₂}

-- ### SimpleEditor

-- Takes direction from first to second component.
simple-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {A₁ A₂ : Set}
  → Direction
  → SimpleEditor V₁ E₁ A₁
  → SimpleEditor V₂ E₂ A₂
  → SimpleEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (A₁ × A₂)
simple-editor-product d (any e₁) (any e₂)
  = any (editor-product d e₁ e₂)

-- ### PartialEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {A₁ A₂ : Set}
  where

  module PartialEditorProduct
    (d : Direction)
    (e₁ : PartialEditor V₁ E₁ A₁)
    (e₂ : PartialEditor V₂ E₂ A₂)
    where

    State
      : Set
    State
      = PartialEditor.State e₁
      × PartialEditor.State e₂

    simple-editor
      : SimpleEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        State
    simple-editor
      = simple-editor-product d
        (PartialEditor.simple-editor e₁)
        (PartialEditor.simple-editor e₂)

    base
      : State
      → Maybe (A₁ × A₂)
    base (s₁ , s₂)
      with PartialEditor.base e₁ s₁
      | PartialEditor.base e₂ s₂
    ... | nothing | _
      = nothing
    ... | _ | nothing
      = nothing
    ... | just x₁ | just x₂
      = just (x₁ , x₂)

  -- Takes direction from first to second component.
  partial-editor-product
    : Direction
    → PartialEditor V₁ E₁ A₁
    → PartialEditor V₂ E₂ A₂
    → PartialEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (A₁ × A₂)
  partial-editor-product d e₁ e₂
    = record {PartialEditorProduct d e₁ e₂}

-- ### SplitEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {C₁ C₂ : Category}
  where

  module SplitEditorProduct
    (d : Direction)
    (e₁ : SplitEditor V₁ E₁ C₁)
    (e₂ : SplitEditor V₂ E₂ C₂)
    where

    StateCategory
      : Category
    StateCategory
      = category-product
        (SplitEditor.StateCategory e₁)
        (SplitEditor.StateCategory e₂)

    editor
      : Editor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateCategory
    editor
      = editor-product d
        (SplitEditor.editor e₁)
        (SplitEditor.editor e₂)

    split-functor
      : SplitFunctor
        StateCategory
        (category-product C₁ C₂)
    split-functor
      = split-functor-product
        (SplitEditor.split-functor e₁)
        (SplitEditor.split-functor e₂)

  -- Takes direction from first to second component.
  split-editor-product
    : Direction
    → SplitEditor V₁ E₁ C₁
    → SplitEditor V₂ E₂ C₂
    → SplitEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (category-product C₁ C₂)
  split-editor-product d e₁ e₂
    = record {SplitEditorProduct d e₁ e₂}

-- ### MainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ A₁ A₂ : Set}
  where

  module MainEditorProduct
    (d : Direction)
    (e₁ : MainEditor V₁ E₁ S₁ A₁)
    (e₂ : MainEditor V₂ E₂ S₂ A₂)
    where

    simple-editor
      : SimpleEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        (A₁ × A₂)
    simple-editor
      = simple-editor-product d
        (MainEditor.simple-editor e₁)
        (MainEditor.simple-editor e₂)

    is-complete
      : A₁ × A₂
      → Bool
    is-complete (s₁ , s₂)
      = MainEditor.is-complete e₁ s₁
      ∧ MainEditor.is-complete e₂ s₂

    split-function
      : SplitFunction
        (S₁ × S₂)
        (A₁ × A₂)
    split-function
      = split-function-product
        (MainEditor.split-function e₁)
        (MainEditor.split-function e₂)

  -- Takes direction from first to second component.
  main-editor-product
    : Direction
    → MainEditor V₁ E₁ S₁ A₁
    → MainEditor V₂ E₂ S₂ A₂
    → MainEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (S₁ × S₂)
      (A₁ × A₂)
  main-editor-product d e₁ e₂
    = record {MainEditorProduct d e₁ e₂}

-- ### SplitMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ P₂ : Set}
  {C₁ C₂ : Category}
  where

  module SplitMainEditorProduct
    (d : Direction)
    (e₁ : SplitMainEditor V₁ E₁ S₁ P₁ C₁)
    (e₂ : SplitMainEditor V₂ E₂ S₂ P₂ C₂)
    where

    StateCategory
      : Category
    StateCategory
      = category-product
        (SplitMainEditor.StateCategory e₁)
        (SplitMainEditor.StateCategory e₂)

    open Category StateCategory using () renaming
      ( Object
        to State
      )

    editor
      : Editor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateCategory
    editor
      = editor-product d
        (SplitMainEditor.editor e₁)
        (SplitMainEditor.editor e₂)

    split-functor
      : SplitFunctor
        StateCategory
        (category-product C₁ C₂)
    split-functor
      = split-functor-product
        (SplitMainEditor.split-functor e₁)
        (SplitMainEditor.split-functor e₂)

    state-split-function
      : SplitFunction
        (S₁ × S₂)
        State
    state-split-function
      = split-function-product
        (SplitMainEditor.state-split-function e₁)
        (SplitMainEditor.state-split-function e₂)

    pure-split-function
      : SplitFunction
        (P₁ × P₂)
        (Category.Object (category-product C₁ C₂))
    pure-split-function
      = split-function-product
        (SplitMainEditor.pure-split-function e₁)
        (SplitMainEditor.pure-split-function e₂)

  -- Takes direction from first to second component.
  split-main-editor-product
    : Direction
    → SplitMainEditor V₁ E₁ S₁ P₁ C₁
    → SplitMainEditor V₂ E₂ S₂ P₂ C₂
    → SplitMainEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (S₁ × S₂)
      (P₁ × P₂)
      (category-product C₁ C₂)
  split-main-editor-product d e₁ e₂
    = record {SplitMainEditorProduct d e₁ e₂}

