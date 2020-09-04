module Prover.Editor.Dependent.Map where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor; dependent-split-functor-compose)
open import Prover.Editor
  using (EventStack; EventStackMap; ViewStack; ViewStackMap)
open import Prover.Editor.Dependent
  using (DependentEditor; DependentPartialEditor; DependentSimpleEditor;
    DependentMainEditor; DependentSplitEditor; DependentSplitMainEditor; cons;
    dependent-editor₀; dependent-editor-tail; dependent-simple-editor₀;
    dependent-simple-editor-tail; nil)
open import Prover.Editor.Map
  using (editor-map-event; editor-map-view; simple-editor-map-event;
    simple-editor-map-view)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction; DependentSimplePartialFunction';
    dependent-simple-partial-function-compose)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction; dependent-simple-split-function-compose)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; dependent-split-function-compose;
    dependent-split-function-compose')
open import Prover.Function.Split
  using (SplitFunction)
open import Prover.Prelude

-- ## View

-- ### DependentEditor

dependent-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → ViewStackMap V W
  → DependentEditor V E C'
  → DependentEditor W E C'
dependent-editor-map-view
  {n = zero} F e
  = nil
    (editor-map-view F
      (dependent-editor₀ e))
dependent-editor-map-view
  {n = suc _} F e
  = cons
    (λ x → dependent-editor-map-view F
      (dependent-editor-tail e x))

-- ### DependentSimpleEditor

dependent-simple-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → ViewStackMap V W
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor W E C'
dependent-simple-editor-map-view
  {n = zero} F e
  = nil
    (simple-editor-map-view F
      (dependent-simple-editor₀ e))
dependent-simple-editor-map-view
  {n = suc _} F e
  = cons
    (λ x → dependent-simple-editor-map-view F
      (dependent-simple-editor-tail e x))

-- ### DependentPartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSet C}
  where

  module DependentPartialEditorMapView
    (F : ViewStackMap V W)
    (e : DependentPartialEditor V E C')
    where

    open DependentPartialEditor e public
      hiding (dependent-simple-editor)

    dependent-simple-editor
      : DependentSimpleEditor W E StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-map-view F
        (DependentPartialEditor.dependent-simple-editor e)

  dependent-partial-editor-map-view
    : ViewStackMap V W
    → DependentPartialEditor V E C'
    → DependentPartialEditor W E C'
  dependent-partial-editor-map-view F e
    = record {DependentPartialEditorMapView F e}

-- ### DependentSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitEditorMapView
    (F : ViewStackMap V W)
    (e : DependentSplitEditor V E C')
    where

    open DependentSplitEditor e public
      hiding (dependent-editor)

    dependent-editor
      : DependentEditor W E StateCategory
    dependent-editor
      = dependent-editor-map-view F
        (DependentSplitEditor.dependent-editor e)

  dependent-split-editor-map-view
    : ViewStackMap V W
    → DependentSplitEditor V E C'
    → DependentSplitEditor W E C'
  dependent-split-editor-map-view F e
    = record {DependentSplitEditorMapView F e}

-- ### DependentMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module DependentMainEditorMapView
    (F : ViewStackMap V W)
    (e : DependentMainEditor V E S C)
    where

    open DependentMainEditor e public
      hiding (dependent-simple-editor)

    dependent-simple-editor
      : DependentSimpleEditor W E StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-map-view F
        (DependentMainEditor.dependent-simple-editor e)

  dependent-main-editor-map-view
    : ViewStackMap V W
    → DependentMainEditor V E S C
    → DependentMainEditor W E S C
  dependent-main-editor-map-view F e
    = record {DependentMainEditorMapView F e}

-- ### DependentSplitMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitMainEditorMapView
    (F : ViewStackMap V W)
    (e : DependentSplitMainEditor V E S P C')
    where

    open DependentSplitMainEditor e public
      hiding (dependent-editor)

    dependent-editor
      : DependentEditor W E StateCategory
    dependent-editor
      = dependent-editor-map-view F
        (DependentSplitMainEditor.dependent-editor e)

  dependent-split-main-editor-map-view
    : ViewStackMap V W
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor W E S P C'
  dependent-split-main-editor-map-view F e
    = record {DependentSplitMainEditorMapView F e}

-- ## Event

-- ### DependentEditor

dependent-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → EventStackMap E F
  → DependentEditor V E C'
  → DependentEditor V F C'
dependent-editor-map-event
  {n = zero} F e
  = nil
    (editor-map-event F
      (dependent-editor₀ e))
dependent-editor-map-event
  {n = suc _} F e
  = cons
    (λ x → dependent-editor-map-event F
      (dependent-editor-tail e x))

-- ### DependentSimpleEditor

dependent-simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → EventStackMap E F
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor V F C'
dependent-simple-editor-map-event
  {n = zero} F e
  = nil
    (simple-editor-map-event F
      (dependent-simple-editor₀ e))
dependent-simple-editor-map-event
  {n = suc _} F e
  = cons
    (λ x → dependent-simple-editor-map-event F
      (dependent-simple-editor-tail e x))

-- ### DependentPartialEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSet C}
  where

  module DependentPartialEditorMapEvent
    (G : EventStackMap E F)
    (e : DependentPartialEditor V E C')
    where

    open DependentPartialEditor e public
      hiding (dependent-simple-editor)

    dependent-simple-editor
      : DependentSimpleEditor V F StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-map-event G
        (DependentPartialEditor.dependent-simple-editor e)

  dependent-partial-editor-map-event
    : EventStackMap E F
    → DependentPartialEditor V E C'
    → DependentPartialEditor V F C'
  dependent-partial-editor-map-event G e
    = record {DependentPartialEditorMapEvent G e}

-- ### DependentSplitEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitEditorMapEvent
    (G : EventStackMap E F)
    (e : DependentSplitEditor V E C')
    where

    open DependentSplitEditor e public
      hiding (dependent-editor)

    dependent-editor
      : DependentEditor V F StateCategory
    dependent-editor
      = dependent-editor-map-event G
        (DependentSplitEditor.dependent-editor e)

  dependent-split-editor-map-event
    : EventStackMap E F
    → DependentSplitEditor V E C'
    → DependentSplitEditor V F C'
  dependent-split-editor-map-event G e
    = record {DependentSplitEditorMapEvent G e}

-- ### DependentMainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module DependentMainEditorMapEvent
    (G : EventStackMap E F)
    (e : DependentMainEditor V E S C)
    where

    open DependentMainEditor e public
      hiding (dependent-simple-editor)

    dependent-simple-editor
      : DependentSimpleEditor V F StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-map-event G
        (DependentMainEditor.dependent-simple-editor e)

  dependent-main-editor-map-event
    : EventStackMap E F
    → DependentMainEditor V E S C
    → DependentMainEditor V F S C
  dependent-main-editor-map-event G e
    = record {DependentMainEditorMapEvent G e}

-- ### DependentSplitMainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitMainEditorMapEvent
    (G : EventStackMap E F)
    (e : DependentSplitMainEditor V E S P C')
    where

    open DependentSplitMainEditor e public
      hiding (dependent-editor)

    dependent-editor
      : DependentEditor V F StateCategory
    dependent-editor
      = dependent-editor-map-event G
        (DependentSplitMainEditor.dependent-editor e)

  dependent-split-main-editor-map-event
    : EventStackMap E F
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor V F S P C'
  dependent-split-main-editor-map-event G e
    = record {DependentSplitMainEditorMapEvent G e}

-- ## State

-- ### DependentMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S T : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module DependentMainEditorMapState
    (F : SplitFunction T S)
    (e : DependentMainEditor V E S C)
    where

    open DependentMainEditor e public
      hiding (dependent-simple-split-function)

    dependent-simple-split-function
      : DependentSimpleSplitFunction T StateSimpleCategory
    dependent-simple-split-function
      = dependent-simple-split-function-compose
        (DependentMainEditor.dependent-simple-split-function e) F

  dependent-main-editor-map-state
    : SplitFunction T S
    → DependentMainEditor V E S C
    → DependentMainEditor V E T C
  dependent-main-editor-map-state F e
    = record {DependentMainEditorMapState F e}

-- ### DependentSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S T P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitMainEditorMapState
    (F : SplitFunction T S)
    (e : DependentSplitMainEditor V E S P C')
    where

    open DependentSplitMainEditor e public
      hiding (state-dependent-split-function)

    state-dependent-split-function
      : DependentSplitFunction T StateCategory
    state-dependent-split-function
      = dependent-split-function-compose
        (DependentSplitMainEditor.state-dependent-split-function e) F

  dependent-split-main-editor-map-state
    : SplitFunction T S
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor V E T P C'
  dependent-split-main-editor-map-state F e
    = record {DependentSplitMainEditorMapState F e}

-- ## Pure

-- ### DependentSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P Q : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentMainEditorMapPure
    (F : SplitFunction Q P)
    (e : DependentSplitMainEditor V E S P C')
    where

    open DependentSplitMainEditor e public
      hiding (pure-dependent-split-function)

    pure-dependent-split-function
      : DependentSplitFunction Q C'
    pure-dependent-split-function
      = dependent-split-function-compose
        (DependentSplitMainEditor.pure-dependent-split-function e) F

  dependent-split-main-editor-map-pure
    : SplitFunction Q P
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor V E S Q C'
  dependent-split-main-editor-map-pure F e
    = record {DependentMainEditorMapPure F e}

-- ## Result

-- ### DependentPartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : DependentSet C}
  where

  module DependentPartialEditorMap
    (F : DependentSimplePartialFunction' C' D')
    (e : DependentPartialEditor V E C')
    where

    open DependentPartialEditor e public
      hiding (dependent-simple-partial-function)

    dependent-simple-partial-function
      : DependentSimplePartialFunction StateSimpleCategory D'
    dependent-simple-partial-function
      = dependent-simple-partial-function-compose F
        (DependentPartialEditor.dependent-simple-partial-function e)

  dependent-partial-editor-map
    : DependentSimplePartialFunction' C' D'
    → DependentPartialEditor V E C'
    → DependentPartialEditor V E D'
  dependent-partial-editor-map F e
    = record {DependentPartialEditorMap F e}

-- ### DependentSplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : DependentCategory C}
  where

  module DependentSplitEditorMap
    (F : DependentSplitFunctor C' D')
    (e : DependentSplitEditor V E C')
    where

    open DependentSplitEditor e public
      hiding (dependent-split-functor)

    dependent-split-functor
      : DependentSplitFunctor StateCategory D'
    dependent-split-functor
      = dependent-split-functor-compose F
        (DependentSplitEditor.dependent-split-functor e)

  dependent-split-editor-map
    : DependentSplitFunctor C' D'
    → DependentSplitEditor V E C'
    → DependentSplitEditor V E D'
  dependent-split-editor-map F e
    = record {DependentSplitEditorMap F e}

-- ### DependentSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : DependentCategory C}
  where

  module DependentSplitMainEditorMap
    (F : DependentSplitFunctor C' D')
    (e : DependentSplitMainEditor V E S P C')
    where

    open DependentSplitMainEditor e public
      hiding (pure-dependent-split-function; dependent-split-functor)

    pure-dependent-split-function
      : DependentSplitFunction P D'
    pure-dependent-split-function
      = dependent-split-function-compose' F
        (DependentSplitMainEditor.pure-dependent-split-function e)

    dependent-split-functor
      : DependentSplitFunctor StateCategory D'
    dependent-split-functor
      = dependent-split-functor-compose F
        (DependentSplitMainEditor.dependent-split-functor e)

  dependent-split-main-editor-map
    : DependentSplitFunctor C' D'
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor V E S P D'
  dependent-split-main-editor-map F e
    = record {DependentSplitMainEditorMap F e}

