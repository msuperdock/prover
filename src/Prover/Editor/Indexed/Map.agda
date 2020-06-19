module Prover.Editor.Indexed.Map where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Base
  using (IndexedSet)
open import Prover.Category.Indexed.Partial.Base
  using (IndexedPartialFunction; IndexedPartialFunction';
    indexed-partial-function-compose)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor; indexed-split-functor-compose)
open import Prover.Category.Indexed.Split.Base
  using (IndexedSimpleSplitFunction; IndexedSplitFunction;
    indexed-simple-split-function-compose; indexed-split-function-compose;
    indexed-split-function-compose')
open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Editor
  using (EventStack; EventStackMap; ViewStack; ViewStackMap)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedPartialEditor; IndexedSimpleEditor;
    IndexedSimpleMainEditor; IndexedSplitEditor; IndexedSplitMainEditor; empty;
    indexed-editor₀; indexed-editor-tail; indexed-simple-editor₀;
    indexed-simple-editor-tail; sigma)
open import Prover.Editor.Map
  using (editor-map-event; editor-map-view; simple-editor-map-event;
    simple-editor-map-view)
open import Prover.Prelude

-- ## View

-- ### IndexedEditor

indexed-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → ViewStackMap V W
  → IndexedEditor V E C'
  → IndexedEditor W E C'
indexed-editor-map-view {n = zero} F e
  = empty
    (editor-map-view F
      (indexed-editor₀ e))
indexed-editor-map-view {n = suc _} F e
  = sigma
    (λ x → indexed-editor-map-view F
      (indexed-editor-tail e x))

-- ### IndexedSimpleEditor

indexed-simple-editor-map-view
  : {V W : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → ViewStackMap V W
  → IndexedSimpleEditor V E C'
  → IndexedSimpleEditor W E C'
indexed-simple-editor-map-view {n = zero} F e
  = empty
    (simple-editor-map-view F
      (indexed-simple-editor₀ e))
indexed-simple-editor-map-view {n = suc _} F e
  = sigma
    (λ x → indexed-simple-editor-map-view F
      (indexed-simple-editor-tail e x))

-- ### IndexedPartialEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSet C}
  where

  module IndexedPartialEditorMapView
    (F : ViewStackMap V W)
    (e : IndexedPartialEditor V E C')
    where

    open IndexedPartialEditor e public
      hiding (indexed-simple-editor)

    indexed-simple-editor
      : IndexedSimpleEditor W E State
    indexed-simple-editor
      = indexed-simple-editor-map-view F
        (IndexedPartialEditor.indexed-simple-editor e)

  indexed-partial-editor-map-view
    : ViewStackMap V W
    → IndexedPartialEditor V E C'
    → IndexedPartialEditor W E C'
  indexed-partial-editor-map-view F e
    = record {IndexedPartialEditorMapView F e}

-- ### IndexedSplitEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitEditorMapView
    (F : ViewStackMap V W)
    (e : IndexedSplitEditor V E C')
    where

    open IndexedSplitEditor e public
      hiding (indexed-editor)

    indexed-editor
      : IndexedEditor W E StateCategory
    indexed-editor
      = indexed-editor-map-view F
        (IndexedSplitEditor.indexed-editor e)

  indexed-split-editor-map-view
    : ViewStackMap V W
    → IndexedSplitEditor V E C'
    → IndexedSplitEditor W E C'
  indexed-split-editor-map-view F e
    = record {IndexedSplitEditorMapView F e}

-- ### IndexedSimpleMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSimpleCategory C}
  where

  module IndexedSimpleMainEditorMapView
    (F : ViewStackMap V W)
    (e : IndexedSimpleMainEditor V E S C')
    where

    open IndexedSimpleMainEditor e public
      hiding (indexed-simple-editor)

    indexed-simple-editor
      : IndexedSimpleEditor W E C'
    indexed-simple-editor
      = indexed-simple-editor-map-view F
        (IndexedSimpleMainEditor.indexed-simple-editor e)

  indexed-simple-main-editor-map-view
    : ViewStackMap V W
    → IndexedSimpleMainEditor V E S C'
    → IndexedSimpleMainEditor W E S C'
  indexed-simple-main-editor-map-view F e
    = record {IndexedSimpleMainEditorMapView F e}

-- ### IndexedSplitMainEditor

module _
  {V W : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitMainEditorMapView
    (F : ViewStackMap V W)
    (e : IndexedSplitMainEditor V E S P C')
    where

    open IndexedSplitMainEditor e public
      hiding (indexed-editor)

    indexed-editor
      : IndexedEditor W E StateCategory
    indexed-editor
      = indexed-editor-map-view F
        (IndexedSplitMainEditor.indexed-editor e)

  indexed-split-main-editor-map-view
    : ViewStackMap V W
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor W E S P C'
  indexed-split-main-editor-map-view F e
    = record {IndexedSplitMainEditorMapView F e}

-- ## Event

-- ### IndexedEditor

indexed-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → EventStackMap E F
  → IndexedEditor V E C'
  → IndexedEditor V F C'
indexed-editor-map-event {n = zero} F e
  = empty
    (editor-map-event F
      (indexed-editor₀ e))
indexed-editor-map-event {n = suc _} F e
  = sigma
    (λ x → indexed-editor-map-event F
      (indexed-editor-tail e x))

-- ### IndexedSimpleEditor

indexed-simple-editor-map-event
  : {V : ViewStack}
  → {E F : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → EventStackMap E F
  → IndexedSimpleEditor V E C'
  → IndexedSimpleEditor V F C'
indexed-simple-editor-map-event {n = zero} F e
  = empty
    (simple-editor-map-event F
      (indexed-simple-editor₀ e))
indexed-simple-editor-map-event {n = suc _} F e
  = sigma
    (λ x → indexed-simple-editor-map-event F
      (indexed-simple-editor-tail e x))

-- ### IndexedPartialEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSet C}
  where

  module IndexedPartialEditorMapEvent
    (G : EventStackMap E F)
    (e : IndexedPartialEditor V E C')
    where

    open IndexedPartialEditor e public
      hiding (indexed-simple-editor)

    indexed-simple-editor
      : IndexedSimpleEditor V F State
    indexed-simple-editor
      = indexed-simple-editor-map-event G
        (IndexedPartialEditor.indexed-simple-editor e)

  indexed-partial-editor-map-event
    : EventStackMap E F
    → IndexedPartialEditor V E C'
    → IndexedPartialEditor V F C'
  indexed-partial-editor-map-event G e
    = record {IndexedPartialEditorMapEvent G e}

-- ### IndexedSplitEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitEditorMapEvent
    (G : EventStackMap E F)
    (e : IndexedSplitEditor V E C')
    where

    open IndexedSplitEditor e public
      hiding (indexed-editor)

    indexed-editor
      : IndexedEditor V F StateCategory
    indexed-editor
      = indexed-editor-map-event G
        (IndexedSplitEditor.indexed-editor e)

  indexed-split-editor-map-event
    : EventStackMap E F
    → IndexedSplitEditor V E C'
    → IndexedSplitEditor V F C'
  indexed-split-editor-map-event G e
    = record {IndexedSplitEditorMapEvent G e}

-- ### IndexedSimpleMainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSimpleCategory C}
  where

  module IndexedSimpleMainEditorMapEvent
    (G : EventStackMap E F)
    (e : IndexedSimpleMainEditor V E S C')
    where

    open IndexedSimpleMainEditor e public
      hiding (indexed-simple-editor)

    indexed-simple-editor
      : IndexedSimpleEditor V F C'
    indexed-simple-editor
      = indexed-simple-editor-map-event G
        (IndexedSimpleMainEditor.indexed-simple-editor e)

  indexed-simple-main-editor-map-event
    : EventStackMap E F
    → IndexedSimpleMainEditor V E S C'
    → IndexedSimpleMainEditor V F S C'
  indexed-simple-main-editor-map-event G e
    = record {IndexedSimpleMainEditorMapEvent G e}

-- ### IndexedSplitMainEditor

module _
  {V : ViewStack}
  {E F : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitMainEditorMapEvent
    (G : EventStackMap E F)
    (e : IndexedSplitMainEditor V E S P C')
    where

    open IndexedSplitMainEditor e public
      hiding (indexed-editor)

    indexed-editor
      : IndexedEditor V F StateCategory
    indexed-editor
      = indexed-editor-map-event G
        (IndexedSplitMainEditor.indexed-editor e)

  indexed-split-main-editor-map-event
    : EventStackMap E F
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor V F S P C'
  indexed-split-main-editor-map-event G e
    = record {IndexedSplitMainEditorMapEvent G e}

-- ## Raw

-- ### IndexedSimpleMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S T : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSimpleCategory C}
  where

  module IndexedSimpleMainEditorMapRaw
    (F : SplitFunction T S)
    (e : IndexedSimpleMainEditor V E S C')
    where

    open IndexedSimpleMainEditor e public
      hiding (indexed-simple-split-function)

    indexed-simple-split-function
      : IndexedSimpleSplitFunction T C'
    indexed-simple-split-function
      = indexed-simple-split-function-compose
        (IndexedSimpleMainEditor.indexed-simple-split-function e) F

  indexed-simple-main-editor-map-raw
    : SplitFunction T S
    → IndexedSimpleMainEditor V E S C'
    → IndexedSimpleMainEditor V E T C'
  indexed-simple-main-editor-map-raw F e
    = record {IndexedSimpleMainEditorMapRaw F e}

-- ### IndexedSplitMainEditor (state)

module _
  {V : ViewStack}
  {E : EventStack}
  {S T P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSimpleMainEditorMapState
    (F : SplitFunction T S)
    (e : IndexedSplitMainEditor V E S P C')
    where

    open IndexedSplitMainEditor e public
      hiding (state-indexed-split-function)

    state-indexed-split-function
      : IndexedSplitFunction T StateCategory
    state-indexed-split-function
      = indexed-split-function-compose
        (IndexedSplitMainEditor.state-indexed-split-function e) F

  indexed-simple-main-editor-map-state
    : SplitFunction T S
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor V E T P C'
  indexed-simple-main-editor-map-state F e
    = record {IndexedSimpleMainEditorMapState F e}

-- ### IndexedSplitMainEditor (pure)

module _
  {V : ViewStack}
  {E : EventStack}
  {S P Q : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSimpleMainEditorMapPure
    (F : SplitFunction Q P)
    (e : IndexedSplitMainEditor V E S P C')
    where

    open IndexedSplitMainEditor e public
      hiding (pure-indexed-split-function)

    pure-indexed-split-function
      : IndexedSplitFunction Q C'
    pure-indexed-split-function
      = indexed-split-function-compose
        (IndexedSplitMainEditor.pure-indexed-split-function e) F

  indexed-simple-main-editor-map-pure
    : SplitFunction Q P
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor V E S Q C'
  indexed-simple-main-editor-map-pure F e
    = record {IndexedSimpleMainEditorMapPure F e}

-- ## Result

-- ### IndexedPartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : IndexedSet C}
  where

  module IndexedPartialEditorMap
    (F : IndexedPartialFunction' C' D')
    (e : IndexedPartialEditor V E C')
    where

    open IndexedPartialEditor e public
      hiding (indexed-partial-function)

    indexed-partial-function
      : IndexedPartialFunction State D'
    indexed-partial-function
      = indexed-partial-function-compose F
        (IndexedPartialEditor.indexed-partial-function e)

  indexed-partial-editor-map
    : IndexedPartialFunction' C' D'
    → IndexedPartialEditor V E C'
    → IndexedPartialEditor V E D'
  indexed-partial-editor-map F e
    = record {IndexedPartialEditorMap F e}

-- ### IndexedSplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : IndexedCategory C}
  where

  module IndexedSplitEditorMap
    (F : IndexedSplitFunctor C' D')
    (e : IndexedSplitEditor V E C')
    where

    open IndexedSplitEditor e public
      hiding (indexed-split-functor)

    indexed-split-functor
      : IndexedSplitFunctor StateCategory D'
    indexed-split-functor
      = indexed-split-functor-compose F
        (IndexedSplitEditor.indexed-split-functor e)

  indexed-split-editor-map
    : IndexedSplitFunctor C' D'
    → IndexedSplitEditor V E C'
    → IndexedSplitEditor V E D'
  indexed-split-editor-map F e
    = record {IndexedSplitEditorMap F e}

-- ### IndexedSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' D' : IndexedCategory C}
  where

  module IndexedSplitMainEditorMap
    (F : IndexedSplitFunctor C' D')
    (e : IndexedSplitMainEditor V E S P C')
    where

    open IndexedSplitMainEditor e public
      hiding (pure-indexed-split-function; indexed-split-functor)

    pure-indexed-split-function
      : IndexedSplitFunction P D'
    pure-indexed-split-function
      = indexed-split-function-compose' F
        (IndexedSplitMainEditor.pure-indexed-split-function e)

    indexed-split-functor
      : IndexedSplitFunctor StateCategory D'
    indexed-split-functor
      = indexed-split-functor-compose F
        (IndexedSplitMainEditor.indexed-split-functor e)

  indexed-split-main-editor-map
    : IndexedSplitFunctor C' D'
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor V E S P D'
  indexed-split-main-editor-map F e
    = record {IndexedSplitMainEditorMap F e}

