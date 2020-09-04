module Prover.Function.Dependent.Split.Sigma.Sum where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory; dependent-category₀)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; cons; dependent-split-function₀; nil)
open import Prover.Function.Split.Sigma.Sum
  using (split-function-sigma-sum)
open import Prover.Prelude

-- ## DependentSplitFunction

dependent-split-function-sigma-sum
  : {n : ℕ}
  → {A₁₁ A₂₁ A₂₂ : Set}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentCategory (chain-category-snoc C₂₁')}
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → DependentSplitFunction A₁₁ C₁₁'
  → DependentSplitFunction A₂₁ C₂₁'
  → DependentSplitFunction A₂₂ C₂₂'
  → DependentSplitFunction
    (A₁₁ ⊔ A₂₁ × A₂₂)
    (dependent-category-sigma-sum C₂₂' F₁)
dependent-split-function-sigma-sum
  {n = zero} {C₂₂' = C₂₂'} _ G₁₁ G₂₁ G₂₂
  = nil
    (split-function-sigma-sum
      (λ x₂₁ → Category.Object (dependent-category₀
        (DependentCategory.tail C₂₂' x₂₁)))
      (dependent-split-function₀ G₁₁)
      (dependent-split-function₀ G₂₁)
      (λ x₂₁ → dependent-split-function₀
        (DependentSplitFunction.tail G₂₂ x₂₁)))
dependent-split-function-sigma-sum
  {n = suc _} F₁ G₁₁ G₂₁ G₂₂
  = cons
    (λ x → dependent-split-function-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentSplitFunction.tail G₁₁ x)
      (DependentSplitFunction.tail G₂₁ x)
      (DependentSplitFunction.tail G₂₂ x))

