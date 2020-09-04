module Prover.Function.Dependent.Simple.Split.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory; dependent-simple-category₀)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; dependent-split-function₀)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction; cons; dependent-simple-split-function₀;
    nil)
open import Prover.Function.Split.Sigma.Sum
  using (split-function-sigma-sum)
open import Prover.Prelude

-- ## DependentSimpleSplitFunction

dependent-simple-split-function-sigma-sum
  : {n : ℕ}
  → {A₁₁ A₂₁ A₂₂ : Set}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentSimpleCategory (chain-category-snoc C₂₁')}
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → DependentSplitFunction A₁₁ C₁₁'
  → DependentSplitFunction A₂₁ C₂₁'
  → DependentSimpleSplitFunction A₂₂ C₂₂'
  → DependentSimpleSplitFunction
    (A₁₁ ⊔ A₂₁ × A₂₂)
    (dependent-simple-category-sigma-sum C₂₂' F₁)
dependent-simple-split-function-sigma-sum
  {n = zero} {C₂₂' = C₂₂'} _ G₁₁ G₂₁ G₂₂
  = nil
    (split-function-sigma-sum
      (λ x₂₁ → dependent-simple-category₀
        (DependentSimpleCategory.tail C₂₂' x₂₁))
      (dependent-split-function₀ G₁₁)
      (dependent-split-function₀ G₂₁)
      (λ x₂₁ → dependent-simple-split-function₀
        (DependentSimpleSplitFunction.tail G₂₂ x₂₁)))
dependent-simple-split-function-sigma-sum
  {n = suc _} F₁ G₁₁ G₂₁ G₂₂
  = cons
    (λ x → dependent-simple-split-function-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentSplitFunction.tail G₁₁ x)
      (DependentSplitFunction.tail G₂₁ x)
      (DependentSimpleSplitFunction.tail G₂₂ x))

