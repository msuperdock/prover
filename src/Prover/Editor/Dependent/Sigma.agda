module Prover.Editor.Dependent.Sigma where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₁)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Dependent.Split.Sigma.Sum
  using (dependent-split-functor-sigma-sum)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Editor
  using (EventStack; ViewStack)
open import Prover.Editor.Dependent
  using (DependentEditor; DependentMainEditor; DependentPartialEditor;
    DependentSimpleEditor; DependentSplitEditor; DependentSplitMainEditor; cons;
    dependent-editor₀; dependent-editor-simple; dependent-editor-tail;
    dependent-split-editor₀; dependent-split-editor-tail;
    dependent-split-main-editor-unmain; nil)
open import Prover.Editor.Dependent.Unit
  using (dependent-editor-unit)
open import Prover.Editor.Sigma
  using (editor-sigma; event-stack-sigma; view-stack-sigma)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Sigma
  using (dependent-set-sigma)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Function.Dependent.Simple.Bool.Sigma.Sum
  using (dependent-simple-bool-function-sigma-sum)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent.Simple.Partial.Sigma.Sum
  using (dependent-simple-partial-function-sigma-sum)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction)
open import Prover.Function.Dependent.Simple.Split.Sigma.Sum
  using (dependent-simple-split-function-sigma-sum)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction)
open import Prover.Function.Dependent.Split.Sigma.Maybe
  using (dependent-split-function-sigma-maybe)
open import Prover.Function.Dependent.Split.Sigma.Sum
  using (dependent-split-function-sigma-sum)
open import Prover.Prelude

-- ## DependentEditor

-- Takes direction from first to second component.
dependent-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : DependentSplitEditor V₁ E₁ C₁')
  → DependentEditor V₂ E₂ C₂'
  → DependentEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-category-sigma-sum C₂'
      (DependentSplitEditor.dependent-split-functor e₁))
dependent-editor-sigma
  {n = zero} {C₂' = C₂'} d e₁ e₂
  = nil
    (editor-sigma
      (dependent-category₁ C₂') d
      (dependent-split-editor₀ e₁)
      (λ x → dependent-editor₀
        (dependent-editor-tail e₂ x)))
dependent-editor-sigma
  {n = suc _} d e₁ e₂
  = cons
    (λ x → dependent-editor-sigma d
      (dependent-split-editor-tail e₁ x)
      (dependent-editor-tail e₂ x))

-- ## DependentSimpleEditor

-- Takes direction from first to second component.
dependent-simple-editor-sigma
  : {V₁ V₂ : ViewStack}
  → {E₁ E₂ : EventStack}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc C₁')}
  → Direction
  → (e₁ : DependentSplitEditor V₁ E₁ C₁')
  → DependentSimpleEditor V₂ E₂ C₂'
  → DependentSimpleEditor
    (view-stack-sigma V₁ V₂)
    (event-stack-sigma E₁ E₂)
    (dependent-simple-category-sigma-sum C₂'
      (DependentSplitEditor.dependent-split-functor e₁))
dependent-simple-editor-sigma d e₁ e₂
  = dependent-editor-simple
  $ dependent-editor-sigma d e₁
    (dependent-editor-unit e₂)

-- ## DependentPartialEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : DependentCategory C}
  {C₂' : DependentSet (chain-category-snoc C₁')}
  where

  module DependentPartialEditorSigma
    (d : Direction)
    (e₁ : DependentSplitEditor V₁ E₁ C₁')
    (e₂ : DependentPartialEditor V₂ E₂ C₂')
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-sigma-sum
        (DependentPartialEditor.StateSimpleCategory e₂)
        (DependentSplitEditor.dependent-split-functor e₁)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-sigma d e₁
        (DependentPartialEditor.dependent-simple-editor e₂)

    dependent-simple-partial-function
      : DependentSimplePartialFunction
        StateSimpleCategory
        (dependent-set-sigma C₁' C₂')
    dependent-simple-partial-function
      = dependent-simple-partial-function-sigma-sum
        (DependentSplitEditor.dependent-split-functor e₁)
        (DependentPartialEditor.dependent-simple-partial-function e₂)

  -- Takes direction from first to second component.
  dependent-partial-editor-sigma
    : Direction
    → DependentSplitEditor V₁ E₁ C₁'
    → DependentPartialEditor V₂ E₂ C₂'
    → DependentPartialEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (dependent-set-sigma C₁' C₂')
  dependent-partial-editor-sigma d e₁ e₂
    = record {DependentPartialEditorSigma d e₁ e₂}

-- ## DependentSplitEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : DependentCategory C}
  {C₂' : DependentCategory (chain-category-snoc C₁')}
  where

  module DependentSplitEditorSigma
    (d : Direction)
    (e₁ : DependentSplitEditor V₁ E₁ C₁')
    (e₂ : DependentSplitEditor V₂ E₂ C₂')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-sigma-sum
        (DependentSplitEditor.StateCategory e₂)
        (DependentSplitEditor.dependent-split-functor e₁)

    dependent-editor
      : DependentEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateCategory
    dependent-editor
      = dependent-editor-sigma d e₁
        (DependentSplitEditor.dependent-editor e₂)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-sigma-maybe C₁' C₂')
    dependent-split-functor
      = dependent-split-functor-sigma-sum
        (DependentSplitEditor.dependent-split-functor e₁)
        (DependentSplitEditor.dependent-split-functor e₂)

  -- Takes direction from first to second component.
  dependent-split-editor-sigma
    : Direction
    → DependentSplitEditor V₁ E₁ C₁'
    → DependentSplitEditor V₂ E₂ C₂'
    → DependentSplitEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (dependent-category-sigma-maybe C₁' C₂')
  dependent-split-editor-sigma d e₁ e₂
    = record {DependentSplitEditorSigma d e₁ e₂}

-- ## DependentMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : DependentCategory C}
  where

  module DependentMainEditorSigma
    (d : Direction)
    (e₁ : DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁')
    (e₂ : DependentMainEditor V₂ E₂ S₂ (chain-category-snoc C₁'))
    where

    StateSimpleCategory
      : DependentSimpleCategory C
    StateSimpleCategory
      = dependent-simple-category-sigma-sum
        (DependentMainEditor.StateSimpleCategory e₂)
        (DependentSplitMainEditor.dependent-split-functor e₁)

    dependent-simple-editor
      : DependentSimpleEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateSimpleCategory
    dependent-simple-editor
      = dependent-simple-editor-sigma d
        (dependent-split-main-editor-unmain e₁)
        (DependentMainEditor.dependent-simple-editor e₂)

    dependent-simple-split-function
      : DependentSimpleSplitFunction
        (S₁ ⊔ P₁ × S₂)
        StateSimpleCategory
    dependent-simple-split-function
      = dependent-simple-split-function-sigma-sum
        (DependentSplitMainEditor.dependent-split-functor e₁)
        (DependentSplitMainEditor.state-dependent-split-function e₁)
        (DependentSplitMainEditor.pure-dependent-split-function e₁)
        (DependentMainEditor.dependent-simple-split-function e₂)

    dependent-simple-bool-function
      : DependentSimpleBoolFunction
        StateSimpleCategory
    dependent-simple-bool-function
      = dependent-simple-bool-function-sigma-sum
        (DependentSplitMainEditor.dependent-split-functor e₁)
        (DependentMainEditor.dependent-simple-bool-function e₂)

  -- Takes direction from first to second component.
  dependent-main-editor-sigma
    : Direction
    → DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁'
    → DependentMainEditor V₂ E₂ S₂ (chain-category-snoc C₁')
    → DependentMainEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (S₁ ⊔ P₁ × S₂) C
  dependent-main-editor-sigma d e₁ e₂
    = record {DependentMainEditorSigma d e₁ e₂}

-- ## DependentSplitMainEditor

module _
  {V₁ V₂ : ViewStack}
  {E₁ E₂ : EventStack}
  {S₁ S₂ P₁ P₂ : Set}
  {n : ℕ}
  {C : ChainCategory n}
  {C₁' : DependentCategory C}
  {C₂' : DependentCategory (chain-category-snoc C₁')}
  where

  module DependentSplitMainEditorSigma
    (d : Direction)
    (e₁ : DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁')
    (e₂ : DependentSplitMainEditor V₂ E₂ S₂ P₂ C₂')
    where

    StateCategory
      : DependentCategory C
    StateCategory
      = dependent-category-sigma-sum
        (DependentSplitMainEditor.StateCategory e₂)
        (DependentSplitMainEditor.dependent-split-functor e₁)

    dependent-editor
      : DependentEditor
        (view-stack-sigma V₁ V₂)
        (event-stack-sigma E₁ E₂)
        StateCategory
    dependent-editor
      = dependent-editor-sigma d 
        (dependent-split-main-editor-unmain e₁)
        (DependentSplitMainEditor.dependent-editor e₂)

    state-dependent-split-function
      : DependentSplitFunction
        (S₁ ⊔ P₁ × S₂)
        StateCategory
    state-dependent-split-function
      = dependent-split-function-sigma-sum
        (DependentSplitMainEditor.dependent-split-functor e₁)
        (DependentSplitMainEditor.state-dependent-split-function e₁)
        (DependentSplitMainEditor.pure-dependent-split-function e₁)
        (DependentSplitMainEditor.state-dependent-split-function e₂)

    pure-dependent-split-function
      : DependentSplitFunction
        (P₁ × P₂)
        (dependent-category-sigma-maybe C₁' C₂')
    pure-dependent-split-function
      = dependent-split-function-sigma-maybe
        (DependentSplitMainEditor.pure-dependent-split-function e₁)
        (DependentSplitMainEditor.pure-dependent-split-function e₂)

    dependent-split-functor
      : DependentSplitFunctor
        StateCategory
        (dependent-category-sigma-maybe C₁' C₂')
    dependent-split-functor
      = dependent-split-functor-sigma-sum
        (DependentSplitMainEditor.dependent-split-functor e₁)
        (DependentSplitMainEditor.dependent-split-functor e₂)

  -- Takes direction from first to second component.
  dependent-split-main-editor-sigma
    : Direction
    → DependentSplitMainEditor V₁ E₁ S₁ P₁ C₁'
    → DependentSplitMainEditor V₂ E₂ S₂ P₂ C₂'
    → DependentSplitMainEditor
      (view-stack-sigma V₁ V₂)
      (event-stack-sigma E₁ E₂)
      (S₁ ⊔ P₁ × S₂)
      (P₁ × P₂)
      (dependent-category-sigma-maybe C₁' C₂')
  dependent-split-main-editor-sigma d e₁ e₂
    = record {DependentSplitMainEditorSigma d e₁ e₂}

