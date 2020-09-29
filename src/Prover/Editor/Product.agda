module Prover.Editor.Product where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding.Product
  using (dependent-encoding-product)
open import Prover.Category.Dependent.Product
  using (dependent-category-product)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Bool.Product
  using (dependent-simple-bool-function-product)
open import Prover.Category.Dependent.Simple.Encoding.Product
  using (dependent-simple-encoding-product)
open import Prover.Category.Dependent.Simple.Partial.Product
  using (dependent-simple-partial-function-product)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Category.Dependent.Simple.Split.Product
  using (dependent-simple-split-functor-product)
open import Prover.Category.Dependent.Split.Product
  using (dependent-split-functor-product)
open import Prover.Category.Product
  using (category-product)
open import Prover.Editor
  using (DependentEditor; DependentInnerEditor; DependentSimpleEditor;
    DependentSimpleInnerEditor; DependentSimpleMainEditor;
    DependentSimplePartialEditor; DependentSimpleSplitEditor;
    DependentSplitEditor; Editor; EventStack; InnerEditor; SimpleInnerEditor;
    SimplePartialEditor; SimpleSplitEditor; SimpleMainEditor; SplitEditor;
    ViewStack; ViewStackMap; dependent-editor-simple)
open import Prover.Editor.Unit
  using (dependent-editor-unit)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Product
  using (dependent-set-product)
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

-- ## Editors (basic)

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

-- ## Editors (dependent)

-- ### DependentEditor

-- Takes direction from first to second component.
dependent-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentEditor V₁ E₁ C₁'
  → DependentEditor V₂ E₂ C₂'
  → DependentEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-category-product C₁' C₂')

dependent-editor-product {n = zero} d e₁ e₂
  = editor-product d e₁ e₂

dependent-editor-product {n = suc _} d e₁ e₂
  = record
  { editor
    = λ x → dependent-editor-product d
      (DependentEditor.editor e₁ x)
      (DependentEditor.editor e₂ x)
  }

-- ### DependentSplitEditor

-- Takes direction from first to second component.
dependent-split-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentSplitEditor V₁ E₁ C₁'
  → DependentSplitEditor V₂ E₂ C₂'
  → DependentSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-category-product C₁' C₂')
dependent-split-editor-product d e₁ e₂
  = record
  { editor
    = dependent-editor-product d
      (DependentSplitEditor.editor e₁)
      (DependentSplitEditor.editor e₂)
  ; split-functor
    = dependent-split-functor-product
      (DependentSplitEditor.split-functor e₁)
      (DependentSplitEditor.split-functor e₂)
  }

-- ### DependentInnerEditor

-- Takes direction from first to second component.
dependent-inner-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (dependent-category-product C₁' C₂')
dependent-inner-editor-product d e₁ e₂
  = record
  { editor
    = dependent-editor-product d
      (DependentInnerEditor.editor e₁)
      (DependentInnerEditor.editor e₂)
  ; state-encoding
    = dependent-encoding-product
      (DependentInnerEditor.state-encoding e₁)
      (DependentInnerEditor.state-encoding e₂)
  ; pure-encoding
    = dependent-encoding-product
      (DependentInnerEditor.pure-encoding e₁)
      (DependentInnerEditor.pure-encoding e₂)
  ; split-functor
    = dependent-split-functor-product
      (DependentInnerEditor.split-functor e₁)
      (DependentInnerEditor.split-functor e₂)
  }

-- ### DependentSimpleEditor

-- Takes direction from first to second component.
dependent-simple-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleEditor V₁ E₁ C₁'
  → DependentSimpleEditor V₂ E₂ C₂'
  → DependentSimpleEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-editor-product d e₁ e₂
  = dependent-editor-simple
  $ dependent-editor-product d
    (dependent-editor-unit e₁)
    (dependent-editor-unit e₂)

-- ### DependentSimplePartialEditor

-- Takes direction from first to second component.
dependent-simple-partial-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSet C}
  → Direction
  → DependentSimplePartialEditor V₁ E₁ C₁'
  → DependentSimplePartialEditor V₂ E₂ C₂'
  → DependentSimplePartialEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-set-product C₁' C₂')
dependent-simple-partial-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimplePartialEditor.editor e₁)
      (DependentSimplePartialEditor.editor e₂)
  ; partial-function
    = dependent-simple-partial-function-product
      (DependentSimplePartialEditor.partial-function e₁)
      (DependentSimplePartialEditor.partial-function e₂)
  }

-- ### DependentSimpleSplitEditor

-- Takes direction from first to second component.
dependent-simple-split-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleSplitEditor V₁ E₁ C₁'
  → DependentSimpleSplitEditor V₂ E₂ C₂'
  → DependentSimpleSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-split-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleSplitEditor.editor e₁)
      (DependentSimpleSplitEditor.editor e₂)
  ; split-functor
    = dependent-simple-split-functor-product
      (DependentSimpleSplitEditor.split-functor e₁)
      (DependentSimpleSplitEditor.split-functor e₂)
  }

-- ### DependentSimpleMainEditor

-- Takes direction from first to second component.
dependent-simple-main-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ : Set}
  → {C : ChainCategory n}
  → Direction
  → DependentSimpleMainEditor V₁ E₁ S₁ C
  → DependentSimpleMainEditor V₂ E₂ S₂ C
  → DependentSimpleMainEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂) C
dependent-simple-main-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleMainEditor.editor e₁)
      (DependentSimpleMainEditor.editor e₂)
  ; state-encoding
    = dependent-simple-encoding-product
      (DependentSimpleMainEditor.state-encoding e₁)
      (DependentSimpleMainEditor.state-encoding e₂)
  ; bool-function
    = dependent-simple-bool-function-product
      (DependentSimpleMainEditor.bool-function e₁)
      (DependentSimpleMainEditor.bool-function e₂)
  }

-- ### DependentSimpleInnerEditor

-- Takes direction from first to second component.
dependent-simple-inner-editor-product
  : {n : ℕ}
  → {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleInnerEditor V₁ E₁ S₁ P₁ C₁'
  → DependentSimpleInnerEditor V₂ E₂ S₂ P₂ C₂'
  → DependentSimpleInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-inner-editor-product d e₁ e₂
  = record
  { editor
    = dependent-simple-editor-product d
      (DependentSimpleInnerEditor.editor e₁)
      (DependentSimpleInnerEditor.editor e₂)
  ; state-encoding
    = dependent-simple-encoding-product
      (DependentSimpleInnerEditor.state-encoding e₁)
      (DependentSimpleInnerEditor.state-encoding e₂)
  ; pure-encoding
    = dependent-simple-encoding-product
      (DependentSimpleInnerEditor.pure-encoding e₁)
      (DependentSimpleInnerEditor.pure-encoding e₂)
  ; split-functor
    = dependent-simple-split-functor-product
      (DependentSimpleInnerEditor.split-functor e₁)
      (DependentSimpleInnerEditor.split-functor e₂)
  }

-- ## Editors (nondependent)

-- ### SplitEditor

-- Takes direction from first to second component.
split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {C₁ C₂ : Category}
  → Direction
  → SplitEditor V₁ E₁ C₁
  → SplitEditor V₂ E₂ C₂
  → SplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (category-product C₁ C₂)
split-editor-product
  = dependent-split-editor-product

-- ### InnerEditor

-- Takes direction from first to second component.
inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ : Set}
  → {C₁ C₂ : Category}
  → Direction
  → InnerEditor V₁ E₁ S₁ P₁ C₁
  → InnerEditor V₂ E₂ S₂ P₂ C₂
  → InnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (category-product C₁ C₂)
inner-editor-product
  = dependent-inner-editor-product

-- ### SimplePartialEditor

-- Takes direction from first to second component.
simple-partial-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {A₁ A₂ : Set}
  → Direction
  → SimplePartialEditor V₁ E₁ A₁
  → SimplePartialEditor V₂ E₂ A₂
  → SimplePartialEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (A₁ × A₂)
simple-partial-editor-product
  = dependent-simple-partial-editor-product

-- ### SimpleSplitEditor

-- Takes direction from first to second component.
simple-split-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {A₁ A₂ : Set}
  → Direction
  → SimpleSplitEditor V₁ E₁ A₁
  → SimpleSplitEditor V₂ E₂ A₂
  → SimpleSplitEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (A₁ × A₂)
simple-split-editor-product
  = dependent-simple-split-editor-product

-- ### SimpleMainEditor

-- Takes direction from first to second component.
simple-main-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ : Set}
  → Direction
  → SimpleMainEditor V₁ E₁ S₁
  → SimpleMainEditor V₂ E₂ S₂
  → SimpleMainEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
simple-main-editor-product
  = dependent-simple-main-editor-product

-- ### SimpleInnerEditor

-- Takes direction from first to second component.
simple-inner-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {S₁ S₂ P₁ P₂ A₁ A₂ : Set}
  → Direction
  → SimpleInnerEditor V₁ E₁ S₁ P₁ A₁
  → SimpleInnerEditor V₂ E₂ S₂ P₂ A₂
  → SimpleInnerEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (S₁ × S₂)
    (P₁ × P₂)
    (A₁ × A₂)
simple-inner-editor-product
  = dependent-simple-inner-editor-product

