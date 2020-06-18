module Prover.Editor.Indexed.Sigma where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀; indexed-dependent-category₀)
open import Prover.Category.Indexed.Sigma.Maybe
  using (indexed-category-sigma-may)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum)
open import Prover.Category.Indexed.Simple
  using (IndexedPartialFunction; IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Sigma
  using (indexed-set-sigma)
open import Prover.Category.Indexed.Simple.Sigma.Sum
  using (indexed-partial-function-sigma-sum; indexed-set-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Split.Sigma.Sum
  using (indexed-split-functor-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedPartialEditor; IndexedSimpleEditor;
    IndexedSplitEditor; empty; indexed-editor₀; indexed-editor-simple;
    indexed-editor-tail; indexed-split-editor₀; indexed-split-editor-tail;
    sigma)
open import Prover.Editor.Indexed.Unit
  using (indexed-editor-unit)
open import Prover.Editor.Sigma
  using (editor-sigma; event-stack-sigma; view-stack-sigma)
open import Prover.Prelude

-- ## IndexedEditor

indexed-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {C₂' : IndexedCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : IndexedSplitEditor V₁ E₁ C₁')
  → IndexedEditor V₂ E₂ C₂'
  → IndexedEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (indexed-category-sigma-sum C₂'
      (IndexedSplitEditor.indexed-split-functor e₁))
indexed-editor-sigma {n = zero} {C₁' = C₁'} {C₂' = C₂'} d e₁ e₂
  = empty
    (editor-sigma
      {C₁ = indexed-category₀ C₁'}
      (indexed-dependent-category₀
        (IndexedCategory.unpack C₂')) d
      (indexed-split-editor₀ e₁)
      (λ x → indexed-editor₀
        (indexed-editor-tail e₂ x)))
indexed-editor-sigma {n = suc _} d e₁ e₂
  = sigma
    (λ x → indexed-editor-sigma d
      (indexed-split-editor-tail e₁ x)
      (indexed-editor-tail e₂ x))

-- ## IndexedSimpleEditor

indexed-simple-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : IndexedCategory C}
  → {C₂' : IndexedSimpleCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : IndexedSplitEditor V₁ E₁ C₁')
  → IndexedSimpleEditor V₂ E₂ C₂'
  → IndexedSimpleEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (indexed-set-sigma-sum C₂' (IndexedSplitEditor.indexed-split-functor e₁))
indexed-simple-editor-sigma d e₁ e₂
  = indexed-editor-simple
  $ indexed-editor-sigma d e₁
    (indexed-editor-unit e₂)

-- ## IndexedPartialEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : IndexedCategory C}
  {C₂' : IndexedSimpleCategory (chain-category-snoc C₁')}
  where

  module IndexedPartialEditorSigma
    (d : Direction)
    (e₁ : IndexedSplitEditor V₁ E₁ C₁')
    (e₂ : IndexedPartialEditor V₂ E₂ C₂')
    where

    State
      : IndexedSimpleCategory C
    State
      = indexed-set-sigma-sum
        (IndexedPartialEditor.State e₂)
        (IndexedSplitEditor.indexed-split-functor e₁)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        State
    indexed-simple-editor
      = indexed-simple-editor-sigma d e₁
        (IndexedPartialEditor.indexed-simple-editor e₂)

    indexed-partial-function
      : IndexedPartialFunction
        State
        (indexed-set-sigma C₁' C₂')
    indexed-partial-function
      = indexed-partial-function-sigma-sum
        (IndexedSplitEditor.indexed-split-functor e₁)
        (IndexedPartialEditor.indexed-partial-function e₂)

  indexed-partial-editor-sigma
    : Direction
    → IndexedSplitEditor V₁ E₁ C₁'
    → IndexedPartialEditor V₂ E₂ C₂'
    → IndexedPartialEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (indexed-set-sigma C₁' C₂')
  indexed-partial-editor-sigma d e₁ e₂
    = record {IndexedPartialEditorSigma d e₁ e₂}

-- ## IndexedSplitEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : IndexedCategory C}
  {C₂' : IndexedCategory (chain-category-snoc C₁')}
  where

  module IndexedSplitEditorSigma
    (d : Direction)
    (e₁ : IndexedSplitEditor V₁ E₁ C₁')
    (e₂ : IndexedSplitEditor V₂ E₂ C₂')
    where

    StateCategory
      : IndexedCategory C
    StateCategory
      = indexed-category-sigma-sum
        (IndexedSplitEditor.StateCategory e₂)
        (IndexedSplitEditor.indexed-split-functor e₁)

    indexed-editor
      : IndexedEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateCategory
    indexed-editor
      = indexed-editor-sigma d e₁
        (IndexedSplitEditor.indexed-editor e₂)

    indexed-split-functor
      : IndexedSplitFunctor
        StateCategory
        (indexed-category-sigma-may C₁' C₂')
    indexed-split-functor
      = indexed-split-functor-sigma-sum
        (IndexedSplitEditor.indexed-split-functor e₁)
        (IndexedSplitEditor.indexed-split-functor e₂)

  indexed-split-editor-sigma
    : Direction
    → IndexedSplitEditor V₁ E₁ C₁'
    → IndexedSplitEditor V₂ E₂ C₂'
    → IndexedSplitEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (indexed-category-sigma-may C₁' C₂')
  indexed-split-editor-sigma d e₁ e₂
    = record {IndexedSplitEditorSigma d e₁ e₂}

