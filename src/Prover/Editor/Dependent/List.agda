module Prover.Editor.Dependent.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.List
  using (dependent-category-list)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Dependent.Split.List
  using (dependent-split-functor-list)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Dependent
  using (DependentEditor; DependentMainEditor; DependentPartialEditor;
    DependentSimpleEditor; DependentSplitEditor; DependentSplitMainEditor; cons;
    dependent-editor₀; dependent-editor-simple; dependent-editor-tail; nil)
open import Prover.Editor.Dependent.Unit
  using (dependent-editor-unit)
open import Prover.Editor.List
  using (editor-list; event-stack-list; view-stack-list)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.List
  using (dependent-set-list)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Function.Dependent.Simple.Bool.List
  using (dependent-simple-bool-function-list)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent.Simple.Partial.List
  using (dependent-simple-partial-function-list)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction)
open import Prover.Function.Dependent.Simple.Split.List
  using (dependent-simple-split-function-list)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction)
open import Prover.Function.Dependent.Split.List
  using (dependent-split-function-list)
open import Prover.Prelude

-- ## DependentEditor

-- Takes direction from earlier to later elements.
dependent-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → Direction
  → DependentEditor V E C'
  → DependentEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-category-list C')
dependent-editor-list
  {n = zero} d e
  = nil
    (editor-list d
      (dependent-editor₀ e))
dependent-editor-list
  {n = suc _} d e
  = cons
    (λ x → dependent-editor-list d
      (dependent-editor-tail e x))

-- ## DependentSimpleEditor

-- Takes direction from earlier to later elements.
dependent-simple-editor-list
  : {V : ViewStack}
  → {E : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → Direction
  → DependentSimpleEditor V E C'
  → DependentSimpleEditor
    (view-stack-list V)
    (event-stack-list E)
    (dependent-simple-category-list C')
dependent-simple-editor-list d e
  = dependent-editor-simple
  $ dependent-editor-list d
    (dependent-editor-unit e)

-- ## DependentPartialEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentSet C}
  where

  module DependentPartialEditorList
    (d : Direction)
    (e : DependentPartialEditor V E C')
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-list
        (DependentPartialEditor.StateSimpleCategory e)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-list d
        (DependentPartialEditor.dependent-simple-editor e)

    dependent-simple-partial-function
      : DependentSimplePartialFunction
        StateSimpleCategory
        (dependent-set-list C')
    dependent-simple-partial-function
      = dependent-simple-partial-function-list
        (DependentPartialEditor.dependent-simple-partial-function e)

  -- Takes direction from earlier to later elements.
  dependent-partial-editor-list
    : Direction
    → DependentPartialEditor V E C'
    → DependentPartialEditor
      (view-stack-list V)
      (event-stack-list E)
      (dependent-set-list C')
  dependent-partial-editor-list d e
    = record {DependentPartialEditorList d e}

-- ## DependentSplitEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitEditorList
    (d : Direction)
    (e : DependentSplitEditor V E C')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-list
        (DependentSplitEditor.StateCategory e)

    dependent-editor
      : DependentEditor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    dependent-editor
      = dependent-editor-list d
        (DependentSplitEditor.dependent-editor e)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-list C')
    dependent-split-functor
      = dependent-split-functor-list
        (DependentSplitEditor.dependent-split-functor e)

  -- Takes direction from earlier to later elements.
  dependent-split-editor-list
    : Direction
    → DependentSplitEditor V E C'
    → DependentSplitEditor
      (view-stack-list V)
      (event-stack-list E)
      (dependent-category-list C')
  dependent-split-editor-list d e
    = record {DependentSplitEditorList d e}

-- ## DependentMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module DependentMainEditorList
    (d : Direction)
    (e : DependentMainEditor V E S C)
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-list
        (DependentMainEditor.StateSimpleCategory e)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-list V)
        (event-stack-list E)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-list d
        (DependentMainEditor.dependent-simple-editor e)

    dependent-simple-split-function
      : DependentSimpleSplitFunction
        (List S)
        StateSimpleCategory
    dependent-simple-split-function
      = dependent-simple-split-function-list
        (DependentMainEditor.dependent-simple-split-function e)

    dependent-simple-bool-function
      : DependentSimpleBoolFunction
        StateSimpleCategory
    dependent-simple-bool-function
      = dependent-simple-bool-function-list
        (DependentMainEditor.dependent-simple-bool-function e)

  -- Takes direction from earlier to later elements.
  dependent-main-editor-list
    : Direction
    → DependentMainEditor V E S C
    → DependentMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S) C
  dependent-main-editor-list d e
    = record {DependentMainEditorList d e}

-- ## DependentSplitMainEditor

module _
  {V : ViewStack}
  {E : EventStack}
  {S P : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C' : DependentCategory C}
  where

  module DependentSplitMainEditorList
    (d : Direction)
    (e : DependentSplitMainEditor V E S P C')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-list
        (DependentSplitMainEditor.StateCategory e)

    dependent-editor
      : DependentEditor
        (view-stack-list V)
        (event-stack-list E)
        StateCategory
    dependent-editor
      = dependent-editor-list d
        (DependentSplitMainEditor.dependent-editor e)

    state-dependent-split-function
      : DependentSplitFunction
        (List S)
        StateCategory
    state-dependent-split-function
      = dependent-split-function-list
        (DependentSplitMainEditor.state-dependent-split-function e)

    pure-dependent-split-function
      : DependentSplitFunction
        (List P)
        (dependent-category-list C')
    pure-dependent-split-function
      = dependent-split-function-list
        (DependentSplitMainEditor.pure-dependent-split-function e)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-list C')
    dependent-split-functor
      = dependent-split-functor-list
        (DependentSplitMainEditor.dependent-split-functor e)

  -- Takes direction from earlier to later elements.
  dependent-split-main-editor-list
    : Direction
    → DependentSplitMainEditor V E S P C'
    → DependentSplitMainEditor
      (view-stack-list V)
      (event-stack-list E)
      (List S)
      (List P)
      (dependent-category-list C')
  dependent-split-main-editor-list d e
    = record {DependentSplitMainEditorList d e}

