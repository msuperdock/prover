module Prover.Editor.Indexed.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.List
  using (indexed-category-list)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.List
  using (indexed-simple-category-list)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Split.List
  using (indexed-split-functor-list)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedMainEditor; IndexedPartialEditor;
    IndexedSimpleEditor; IndexedSplitEditor; IndexedSplitMainEditor; empty;
    indexed-editor₀; indexed-editor-simple; indexed-editor-tail; sigma)
open import Prover.Editor.Indexed.Unit
  using (indexed-editor-unit)
open import Prover.Editor.List
  using (editor-list; event-stack-list; view-stack-list)
open import Prover.Function.Indexed
  using (IndexedSet)
open import Prover.Function.Indexed.List
  using (indexed-set-list)
open import Prover.Function.Indexed.Simple.Bool
  using (IndexedSimpleBoolFunction)
open import Prover.Function.Indexed.Simple.Bool.List
  using (indexed-simple-bool-function-list)
open import Prover.Function.Indexed.Simple.Partial
  using (IndexedSimplePartialFunction)
open import Prover.Function.Indexed.Simple.Partial.List
  using (indexed-simple-partial-function-list)
open import Prover.Function.Indexed.Simple.Split
  using (IndexedSimpleSplitFunction)
open import Prover.Function.Indexed.Simple.Split.List
  using (indexed-simple-split-function-list)
open import Prover.Function.Indexed.Split
  using (IndexedSplitFunction)
open import Prover.Function.Indexed.Split.List
  using (indexed-split-function-list)
open import Prover.Prelude

-- ## IndexedEditor

-- Takes direction from earlier to later elements.
indexed-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → Direction
  → IndexedEditor V E C'
  → IndexedEditor
    (view-stack-list V)
    (event-stack-list E)
    (indexed-category-list C')
indexed-editor-list {n = zero} d e
  = empty
    (editor-list d
      (indexed-editor₀ e))
indexed-editor-list {n = suc _} d e
  = sigma
    (λ x → indexed-editor-list d
      (indexed-editor-tail e x))

-- ## IndexedSimpleEditor

-- Takes direction from earlier to later elements.
indexed-simple-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → Direction
  → IndexedSimpleEditor V E C'
  → IndexedSimpleEditor
    (view-stack-list V)
    (event-stack-list E)
    (indexed-simple-category-list C')
indexed-simple-editor-list d e
  = indexed-editor-simple
  $ indexed-editor-list d
    (indexed-editor-unit e)

-- ## IndexedPartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedSet C}
  where

  module IndexedPartialEditorList
    (d : Direction)
    (e : IndexedPartialEditor V E C')
    where

    StateSimpleCategory
      : IndexedSimpleCategory C
    StateSimpleCategory
      = indexed-simple-category-list
        (IndexedPartialEditor.StateSimpleCategory e)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        StateSimpleCategory
    indexed-simple-editor
      = indexed-simple-editor-list d
        (IndexedPartialEditor.indexed-simple-editor e)

    indexed-simple-partial-function
      : IndexedSimplePartialFunction
        StateSimpleCategory
        (indexed-set-list C')
    indexed-simple-partial-function
      = indexed-simple-partial-function-list
        (IndexedPartialEditor.indexed-simple-partial-function e)

  -- Takes direction from earlier to later elements.
  indexed-partial-editor-list
    : Direction
    → IndexedPartialEditor V E C'
    → IndexedPartialEditor
      (view-stack-list V)
      (event-stack-list E)
      (indexed-set-list C')
  indexed-partial-editor-list d e
    = record {IndexedPartialEditorList d e}

-- ## IndexedSplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitEditorList
    (d : Direction)
    (e : IndexedSplitEditor V E C')
    where

    StateCategory
      : IndexedCategory C
    StateCategory
      = indexed-category-list
        (IndexedSplitEditor.StateCategory e)

    indexed-editor
      : IndexedEditor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    indexed-editor
      = indexed-editor-list d
        (IndexedSplitEditor.indexed-editor e)

    indexed-split-functor
      : IndexedSplitFunctor
        StateCategory
        (indexed-category-list C')
    indexed-split-functor
      = indexed-split-functor-list
        (IndexedSplitEditor.indexed-split-functor e)

  -- Takes direction from earlier to later elements.
  indexed-split-editor-list
    : Direction
    → IndexedSplitEditor V E C'
    → IndexedSplitEditor
      (view-stack-list V)
      (event-stack-list E)
      (indexed-category-list C')
  indexed-split-editor-list d e
    = record {IndexedSplitEditorList d e}

-- ## IndexedMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module IndexedMainEditorList
    (d : Direction)
    (e : IndexedMainEditor V E S C)
    where

    StateSimpleCategory
      : IndexedSimpleCategory C
    StateSimpleCategory
      = indexed-simple-category-list
        (IndexedMainEditor.StateSimpleCategory e)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        StateSimpleCategory
    indexed-simple-editor
      = indexed-simple-editor-list d
        (IndexedMainEditor.indexed-simple-editor e)

    indexed-simple-split-function
      : IndexedSimpleSplitFunction
        (List S)
        StateSimpleCategory
    indexed-simple-split-function
      = indexed-simple-split-function-list
        (IndexedMainEditor.indexed-simple-split-function e)

    indexed-simple-bool-function
      : IndexedSimpleBoolFunction
        StateSimpleCategory
    indexed-simple-bool-function
      = indexed-simple-bool-function-list
        (IndexedMainEditor.indexed-simple-bool-function e)

  -- Takes direction from earlier to later elements.
  indexed-main-editor-list
    : Direction
    → IndexedMainEditor V E S C
    → IndexedMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S) C
  indexed-main-editor-list d e
    = record {IndexedMainEditorList d e}

-- ## IndexedSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : IndexedCategory C}
  where

  module IndexedSplitMainEditorList
    (d : Direction)
    (e : IndexedSplitMainEditor V E S P C')
    where

    StateCategory
      : IndexedCategory C
    StateCategory
      = indexed-category-list
        (IndexedSplitMainEditor.StateCategory e)

    indexed-editor
      : IndexedEditor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    indexed-editor
      = indexed-editor-list d
        (IndexedSplitMainEditor.indexed-editor e)

    state-indexed-split-function
      : IndexedSplitFunction
        (List S)
        StateCategory
    state-indexed-split-function
      = indexed-split-function-list
        (IndexedSplitMainEditor.state-indexed-split-function e)

    pure-indexed-split-function
      : IndexedSplitFunction
        (List P)
        (indexed-category-list C')
    pure-indexed-split-function
      = indexed-split-function-list
        (IndexedSplitMainEditor.pure-indexed-split-function e)

    indexed-split-functor
      : IndexedSplitFunctor
        StateCategory
        (indexed-category-list C')
    indexed-split-functor
      = indexed-split-functor-list
        (IndexedSplitMainEditor.indexed-split-functor e)

  -- Takes direction from earlier to later elements.
  indexed-split-main-editor-list
    : Direction
    → IndexedSplitMainEditor V E S P C'
    → IndexedSplitMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
      (List P)
      (indexed-category-list C')
  indexed-split-main-editor-list d e
    = record {IndexedSplitMainEditorList d e}

