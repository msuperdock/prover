module Prover.Editor.Dependent.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Product
  using (dependent-category-product)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Dependent.Split.Product
  using (dependent-split-functor-product)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Dependent
  using (DependentEditor; DependentMainEditor; DependentPartialEditor;
    DependentSimpleEditor; DependentSplitEditor; DependentSplitMainEditor; cons;
    dependent-editor₀; dependent-editor-simple; dependent-editor-tail; nil)
open import Prover.Editor.Dependent.Unit
  using (dependent-editor-unit)
open import Prover.Editor.Product
  using (event-stack-product; view-stack-product; editor-product)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Function.Dependent.Simple.Bool.Product
  using (dependent-simple-bool-function-product)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent.Simple.Partial.Product
  using (dependent-simple-partial-function-product)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction)
open import Prover.Function.Dependent.Simple.Split.Product
  using (dependent-simple-split-function-product)
open import Prover.Function.Dependent.Product
  using (dependent-set-product)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction)
open import Prover.Function.Dependent.Split.Product
  using (dependent-split-function-product)
open import Prover.Prelude

-- ## DependentEditor

-- Takes direction from first to second component.
dependent-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → Direction
  → DependentEditor V₁ E₁ C₁'
  → DependentEditor V₂ E₂ C₂'
  → DependentEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (dependent-category-product C₁' C₂')
dependent-editor-product
  {n = zero} d e₁ e₂
  = nil
    (editor-product d
      (dependent-editor₀ e₁)
      (dependent-editor₀ e₂))
dependent-editor-product
  {n = suc _} d e₁ e₂
  = cons
    (λ x → dependent-editor-product d
      (dependent-editor-tail e₁ x)
      (dependent-editor-tail e₂ x))

-- ## DependentSimpleEditor

-- Takes direction from first to second component.
dependent-simple-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
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

-- ## DependentPartialEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' C₂' : DependentSet C}
  where

  module DependentPartialEditorProduct
    (d : Direction)
    (e₁ : DependentPartialEditor V₁ E₁ C₁')
    (e₂ : DependentPartialEditor V₂ E₂ C₂')
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-product
        (DependentPartialEditor.StateSimpleCategory e₁)
        (DependentPartialEditor.StateSimpleCategory e₂)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-product d
        (DependentPartialEditor.dependent-simple-editor e₁)
        (DependentPartialEditor.dependent-simple-editor e₂)

    dependent-simple-partial-function
      : DependentSimplePartialFunction
        StateSimpleCategory
        (dependent-set-product C₁' C₂')
    dependent-simple-partial-function
      = dependent-simple-partial-function-product
        (DependentPartialEditor.dependent-simple-partial-function e₁)
        (DependentPartialEditor.dependent-simple-partial-function e₂)

  -- Takes direction from first to second component.
  dependent-partial-editor-product
    : Direction
    → DependentPartialEditor V₁ E₁ C₁'
    → DependentPartialEditor V₂ E₂ C₂'
    → DependentPartialEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (dependent-set-product C₁' C₂')
  dependent-partial-editor-product d e₁ e₂
    = record {DependentPartialEditorProduct d e₁ e₂}

-- ## DependentSplitEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' C₂' : DependentCategory C}
  where

  module DependentSplitEditorProduct
    (d : Direction)
    (e₁ : DependentSplitEditor V₁ E₁ C₁')
    (e₂ : DependentSplitEditor V₂ E₂ C₂')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-product
        (DependentSplitEditor.StateCategory e₁)
        (DependentSplitEditor.StateCategory e₂)

    dependent-editor
      : DependentEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateCategory
    dependent-editor
      = dependent-editor-product d
        (DependentSplitEditor.dependent-editor e₁)
        (DependentSplitEditor.dependent-editor e₂)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-product C₁' C₂') 
    dependent-split-functor
      = dependent-split-functor-product
        (DependentSplitEditor.dependent-split-functor e₁)
        (DependentSplitEditor.dependent-split-functor e₂)

  -- Takes direction from first to second component.
  dependent-split-editor-product
    : Direction
    → DependentSplitEditor V₁ E₁ C₁'
    → DependentSplitEditor V₂ E₂ C₂'
   → DependentSplitEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (dependent-category-product C₁' C₂')
  dependent-split-editor-product d e₁ e₂
    = record {DependentSplitEditorProduct d e₁ e₂}

-- ## DependentMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  where

  module DependentMainEditorProduct
    (d : Direction)
    (e₁ : DependentMainEditor V₁ E₁ S₁ C)
    (e₂ : DependentMainEditor V₂ E₂ S₂ C)
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-product
        (DependentMainEditor.StateSimpleCategory e₁)
        (DependentMainEditor.StateSimpleCategory e₂)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-product d
        (DependentMainEditor.dependent-simple-editor e₁)
        (DependentMainEditor.dependent-simple-editor e₂)

    dependent-simple-split-function
      : DependentSimpleSplitFunction
        (S₁ × S₂)
        StateSimpleCategory
    dependent-simple-split-function
      = dependent-simple-split-function-product
        (DependentMainEditor.dependent-simple-split-function e₁)
        (DependentMainEditor.dependent-simple-split-function e₂)

    dependent-simple-bool-function
      : DependentSimpleBoolFunction
        StateSimpleCategory
    dependent-simple-bool-function
      = dependent-simple-bool-function-product
        (DependentMainEditor.dependent-simple-bool-function e₁)
        (DependentMainEditor.dependent-simple-bool-function e₂)

  -- Takes direction from first to second component.
  dependent-main-editor-product
    : Direction
    → DependentMainEditor V₁ E₁ S₁ C
    → DependentMainEditor V₂ E₂ S₂ C
    → DependentMainEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (S₁ × S₂) C
  dependent-main-editor-product d e₁ e₂
    = record {DependentMainEditorProduct d e₁ e₂}

-- ## DependentSplitMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ P₂ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' C₂' : DependentCategory C}
  where

  module DependentSplitMainEditorProduct
    (d : Direction)
    (e₁ : DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁')
    (e₂ : DependentSplitMainEditor V₂ E₂ S₂ P₂ C₂')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-product
        (DependentSplitMainEditor.StateCategory e₁)
        (DependentSplitMainEditor.StateCategory e₂)

    dependent-editor
      : DependentEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateCategory
    dependent-editor
      = dependent-editor-product d
        (DependentSplitMainEditor.dependent-editor e₁)
        (DependentSplitMainEditor.dependent-editor e₂)

    state-dependent-split-function
      : DependentSplitFunction
        (S₁ × S₂)
        StateCategory
    state-dependent-split-function
      = dependent-split-function-product
        (DependentSplitMainEditor.state-dependent-split-function e₁)
        (DependentSplitMainEditor.state-dependent-split-function e₂)

    pure-dependent-split-function
      : DependentSplitFunction
        (P₁ × P₂)
        (dependent-category-product C₁' C₂')
    pure-dependent-split-function
      = dependent-split-function-product
        (DependentSplitMainEditor.pure-dependent-split-function e₁)
        (DependentSplitMainEditor.pure-dependent-split-function e₂)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-product C₁' C₂')
    dependent-split-functor
      = dependent-split-functor-product
        (DependentSplitMainEditor.dependent-split-functor e₁)
        (DependentSplitMainEditor.dependent-split-functor e₂)

  -- Takes direction from first to second component.
  dependent-split-main-editor-product
    : Direction
    → DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁'
    → DependentSplitMainEditor V₂ E₂ S₂ P₂ C₂'
    → DependentSplitMainEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (S₁ × S₂)
      (P₁ × P₂)
      (dependent-category-product C₁' C₂')
  dependent-split-main-editor-product d e₁ e₂
    = record {DependentSplitMainEditorProduct d e₁ e₂}

