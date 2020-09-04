module Prover.Function.Dependent.Simple.Bool.Sigma.Sum where

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
open import Prover.Function.Bool.Sigma.Sum
  using (bool-function-sigma-sum)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction; cons; dependent-simple-bool-function₀;
    nil)
open import Prover.Prelude

dependent-simple-bool-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentSimpleCategory (chain-category-snoc C₂₁')} 
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → DependentSimpleBoolFunction C₂₂'
  → DependentSimpleBoolFunction (dependent-simple-category-sigma-sum C₂₂' F₁)
dependent-simple-bool-function-sigma-sum
  {n = zero} {C₂₂' = C₂₂'} _ G₂₂
  = nil
    (bool-function-sigma-sum
      (λ x₂₁ → dependent-simple-category₀
        (DependentSimpleCategory.tail C₂₂' x₂₁))
      (λ x₂₁ → dependent-simple-bool-function₀
        (DependentSimpleBoolFunction.tail G₂₂ x₂₁)))
dependent-simple-bool-function-sigma-sum
  {n = suc _} F₁ G₂₂
  = cons
    (λ x → dependent-simple-bool-function-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentSimpleBoolFunction.tail G₂₂ x))

