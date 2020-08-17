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
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Sigma.Sum
  using (indexed-simple-category-sigma-sum)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Split.Sigma.Sum
  using (indexed-split-functor-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Indexed
  using (IndexedEditor; IndexedMainEditor; IndexedPartialEditor;
    IndexedSimpleEditor; IndexedSplitEditor; IndexedSplitMainEditor; empty;
    indexed-editor₀; indexed-editor-simple; indexed-editor-tail;
    indexed-split-editor₀; indexed-split-editor-tail;
    indexed-split-main-editor-unmain; sigma)
open import Prover.Editor.Indexed.Unit
  using (indexed-editor-unit)
open import Prover.Editor.Sigma
  using (editor-sigma; event-stack-sigma; view-stack-sigma)
open import Prover.Function.Indexed
  using (IndexedSet)
open import Prover.Function.Indexed.Partial
  using (IndexedPartialFunction)
open import Prover.Function.Indexed.Partial.Sigma.Sum
  using (indexed-partial-function-sigma-sum)
open import Prover.Function.Indexed.Sigma
  using (indexed-set-sigma)
open import Prover.Function.Indexed.Split
  using (IndexedSimpleSplitFunction; IndexedSplitFunction)
open import Prover.Function.Indexed.Split.Sigma.Maybe
  using (indexed-split-function-sigma-may)
open import Prover.Function.Indexed.Split.Sigma.Sum
  using (indexed-simple-split-function-sigma-sum;
    indexed-split-function-sigma-sum)
open import Prover.Prelude

-- ## IndexedEditor

-- Takes direction from first to second component.
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

-- Takes direction from first to second component.
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
    (indexed-simple-category-sigma-sum C₂'
      (IndexedSplitEditor.indexed-split-functor e₁))
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
  {C₂' : IndexedSet (chain-category-snoc C₁')}
  where

  module IndexedPartialEditorSigma
    (d : Direction)
    (e₁ : IndexedSplitEditor V₁ E₁ C₁')
    (e₂ : IndexedPartialEditor V₂ E₂ C₂')
    where

    StateSimpleCategory
      : IndexedSimpleCategory C
    StateSimpleCategory
      = indexed-simple-category-sigma-sum
        (IndexedPartialEditor.StateSimpleCategory e₂)
        (IndexedSplitEditor.indexed-split-functor e₁)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateSimpleCategory
    indexed-simple-editor
      = indexed-simple-editor-sigma d e₁
        (IndexedPartialEditor.indexed-simple-editor e₂)

    indexed-partial-function
      : IndexedPartialFunction
        StateSimpleCategory
        (indexed-set-sigma C₁' C₂')
    indexed-partial-function
      = indexed-partial-function-sigma-sum
        (IndexedSplitEditor.indexed-split-functor e₁)
        (IndexedPartialEditor.indexed-partial-function e₂)

  -- Takes direction from first to second component.
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

  -- Takes direction from first to second component.
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

-- ## IndexedMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : IndexedCategory C}
  where

  module IndexedMainEditorSigma
    (d : Direction)
    (e₁ : IndexedSplitMainEditor V₁ E₁ S₁ P₁ C₁')
    (e₂ : IndexedMainEditor V₂ E₂ S₂ (chain-category-snoc C₁'))
    where

    StateSimpleCategory
      : IndexedSimpleCategory C
    StateSimpleCategory
      = indexed-simple-category-sigma-sum
        (IndexedMainEditor.StateSimpleCategory e₂)
        (IndexedSplitMainEditor.indexed-split-functor e₁)

    indexed-simple-editor
      : IndexedSimpleEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateSimpleCategory
    indexed-simple-editor
      = indexed-simple-editor-sigma d
        (indexed-split-main-editor-unmain e₁)
        (IndexedMainEditor.indexed-simple-editor e₂)

    indexed-simple-split-function
      : IndexedSimpleSplitFunction
        (S₁ ⊔ P₁ × S₂)
        StateSimpleCategory
    indexed-simple-split-function
      = indexed-simple-split-function-sigma-sum
        (IndexedSplitMainEditor.indexed-split-functor e₁)
        (IndexedSplitMainEditor.state-indexed-split-function e₁)
        (IndexedSplitMainEditor.pure-indexed-split-function e₁)
        (IndexedMainEditor.indexed-simple-split-function e₂)

  -- Takes direction from first to second component.
  indexed-main-editor-sigma
    : Direction
    → IndexedSplitMainEditor V₁ E₁ S₁ P₁ C₁'
    → IndexedMainEditor V₂ E₂ S₂ (chain-category-snoc C₁')
    → IndexedMainEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (S₁ ⊔ P₁ × S₂) C
  indexed-main-editor-sigma d e₁ e₂
    = record {IndexedMainEditorSigma d e₁ e₂}

-- ## IndexedSplitMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ P₂ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : IndexedCategory C}
  {C₂' : IndexedCategory (chain-category-snoc C₁')}
  where

  module IndexedSplitMainEditorSigma
    (d : Direction)
    (e₁ : IndexedSplitMainEditor V₁ E₁ S₁ P₁ C₁')
    (e₂ : IndexedSplitMainEditor V₂ E₂ S₂ P₂ C₂')
    where

    StateCategory
      : IndexedCategory C
    StateCategory
      = indexed-category-sigma-sum
        (IndexedSplitMainEditor.StateCategory e₂)
        (IndexedSplitMainEditor.indexed-split-functor e₁)

    indexed-editor
      : IndexedEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateCategory
    indexed-editor
      = indexed-editor-sigma d 
        (indexed-split-main-editor-unmain e₁)
        (IndexedSplitMainEditor.indexed-editor e₂)

    state-indexed-split-function
      : IndexedSplitFunction
        (S₁ ⊔ P₁ × S₂)
        StateCategory
    state-indexed-split-function
      = indexed-split-function-sigma-sum
        (IndexedSplitMainEditor.indexed-split-functor e₁)
        (IndexedSplitMainEditor.state-indexed-split-function e₁)
        (IndexedSplitMainEditor.pure-indexed-split-function e₁)
        (IndexedSplitMainEditor.state-indexed-split-function e₂)

    pure-indexed-split-function
      : IndexedSplitFunction
        (P₁ × P₂)
        (indexed-category-sigma-may C₁' C₂')
    pure-indexed-split-function
      = indexed-split-function-sigma-may
        (IndexedSplitMainEditor.pure-indexed-split-function e₁)
        (IndexedSplitMainEditor.pure-indexed-split-function e₂)

    indexed-split-functor
      : IndexedSplitFunctor
        StateCategory
        (indexed-category-sigma-may C₁' C₂')
    indexed-split-functor
      = indexed-split-functor-sigma-sum
        (IndexedSplitMainEditor.indexed-split-functor e₁)
        (IndexedSplitMainEditor.indexed-split-functor e₂)

  -- Takes direction from first to second component.
  indexed-split-main-editor-sigma
    : Direction
    → IndexedSplitMainEditor V₁ E₁ S₁ P₁ C₁'
    → IndexedSplitMainEditor V₂ E₂ S₂ P₂ C₂'
    → IndexedSplitMainEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (S₁ ⊔ P₁ × S₂)
      (P₁ × P₂)
      (indexed-category-sigma-may C₁' C₂')
  indexed-split-main-editor-sigma d e₁ e₂
    = record {IndexedSplitMainEditorSigma d e₁ e₂}

