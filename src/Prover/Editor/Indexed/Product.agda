module Prover.Editor.Indexed.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Base
  using (IndexedSet)
open import Prover.Category.Indexed.Base.Product
  using (indexed-set-product)
open import Prover.Category.Indexed.Partial.Base
  using (IndexedPartialFunction)
open import Prover.Category.Indexed.Partial.Base.Product
  using (indexed-partial-function-product)
open import Prover.Category.Indexed.Product
  using (indexed-category-product)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Split.Product
  using (indexed-split-functor-product)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedPartialEditor; IndexedSimpleEditor;
    IndexedSplitEditor; empty; indexed-editor₀; indexed-editor-simple;
    indexed-editor-tail; sigma)
open import Prover.Editor.Indexed.Unit
  using (indexed-editor-unit)
open import Prover.Editor.Product
  using (event-stack-product; view-stack-product; editor-product)
open import Prover.Prelude

-- ## IndexedEditor

-- Takes direction from first to second component.
indexed-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedCategory C}
  → Direction
  → IndexedEditor V₁ E₁ C₁'
  → IndexedEditor V₂ E₂ C₂'
  → IndexedEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (indexed-category-product C₁' C₂')
indexed-editor-product {n = zero} d e₁ e₂
  = empty
    (editor-product d
      (indexed-editor₀ e₁)
      (indexed-editor₀ e₂))
indexed-editor-product {n = suc _} d e₁ e₂
  = sigma
    (λ x → indexed-editor-product d
      (indexed-editor-tail e₁ x)
      (indexed-editor-tail e₂ x))

-- ## IndexedSimpleEditor

-- Takes direction from first to second component.
indexed-simple-editor-product
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedSimpleCategory C}
  → Direction
  → IndexedSimpleEditor V₁ E₁ C₁'
  → IndexedSimpleEditor V₂ E₂ C₂'
  → IndexedSimpleEditor
    (view-stack-product V₁ V₂)
    (event-stack-product E₁ E₂)
    (indexed-simple-category-product C₁' C₂')
indexed-simple-editor-product d e₁ e₂
  = indexed-editor-simple
  $ indexed-editor-product d
    (indexed-editor-unit e₁)
    (indexed-editor-unit e₂)

-- ## IndexedPartialEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' C₂' : IndexedSet C}
  where

  module IndexedPartialEditorProduct
    (d : Direction)
    (e₁ : IndexedPartialEditor V₁ E₁ C₁')
    (e₂ : IndexedPartialEditor V₂ E₂ C₂')
    where

    StateSimpleCategory
      : IndexedSimpleCategory C
    StateSimpleCategory
      = indexed-simple-category-product
        (IndexedPartialEditor.StateSimpleCategory e₁)
        (IndexedPartialEditor.StateSimpleCategory e₂)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateSimpleCategory
    indexed-simple-editor
      = indexed-simple-editor-product d
        (IndexedPartialEditor.indexed-simple-editor e₁)
        (IndexedPartialEditor.indexed-simple-editor e₂)

    indexed-partial-function
      : IndexedPartialFunction
        StateSimpleCategory
        (indexed-set-product C₁' C₂')
    indexed-partial-function
      = indexed-partial-function-product
        (IndexedPartialEditor.indexed-partial-function e₁)
        (IndexedPartialEditor.indexed-partial-function e₂)

  -- Takes direction from first to second component.
  indexed-partial-editor-product
    : Direction
    → IndexedPartialEditor V₁ E₁ C₁'
    → IndexedPartialEditor V₂ E₂ C₂'
    → IndexedPartialEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (indexed-set-product C₁' C₂')
  indexed-partial-editor-product d e₁ e₂
    = record {IndexedPartialEditorProduct d e₁ e₂}

-- ## IndexedSplitEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' C₂' : IndexedCategory C}
  where

  module IndexedSplitEditorProduct
    (d : Direction)
    (e₁ : IndexedSplitEditor V₁ E₁ C₁')
    (e₂ : IndexedSplitEditor V₂ E₂ C₂')
    where

    StateCategory
      : IndexedCategory C
    StateCategory
      = indexed-category-product
        (IndexedSplitEditor.StateCategory e₁)
        (IndexedSplitEditor.StateCategory e₂)

    indexed-editor
      : IndexedEditor
        (view-stack-product V₁ V₂)
        (event-stack-product E₁ E₂)
        StateCategory
    indexed-editor
      = indexed-editor-product d
        (IndexedSplitEditor.indexed-editor e₁)
        (IndexedSplitEditor.indexed-editor e₂)

    indexed-split-functor
      : IndexedSplitFunctor
        StateCategory
        (indexed-category-product C₁' C₂') 
    indexed-split-functor
      = indexed-split-functor-product
        (IndexedSplitEditor.indexed-split-functor e₁)
        (IndexedSplitEditor.indexed-split-functor e₂)

  -- Takes direction from first to second component.
  indexed-split-editor-product
    : Direction
    → IndexedSplitEditor V₁ E₁ C₁'
    → IndexedSplitEditor V₂ E₂ C₂'
    → IndexedSplitEditor
      (view-stack-product V₁ V₂)
      (event-stack-product E₁ E₂)
      (indexed-category-product C₁' C₂')
  indexed-split-editor-product d e₁ e₂
    = record {IndexedSplitEditorProduct d e₁ e₂}

