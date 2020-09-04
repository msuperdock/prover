module Prover.Function.Dependent.Simple.Partial.Sigma.Sum where

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
open import Prover.Function.Dependent
  using (DependentSet; dependent-set₀)
open import Prover.Function.Dependent.Sigma
  using (dependent-set-sigma)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction; cons;
    dependent-simple-partial-function₀; nil)
open import Prover.Function.Partial.Sigma.Sum
  using (partial-function-sigma-sum)
open import Prover.Prelude

-- ## DependentSimplePartialFunction

dependent-simple-partial-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : DependentCategory C}
  → {C₂' : DependentSimpleCategory (chain-category-snoc D₁')}
  → {D₂' : DependentSet (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSimplePartialFunction C₂' D₂'
  → DependentSimplePartialFunction
    (dependent-simple-category-sigma-sum C₂' F₁)
    (dependent-set-sigma D₁' D₂')
dependent-simple-partial-function-sigma-sum
  {n = zero} {C₂' = C₂'} {D₂' = D₂'} _ F₂
  = nil
    (partial-function-sigma-sum
      (λ y₁ → dependent-simple-category₀
        (DependentSimpleCategory.tail C₂' y₁))
      (λ y₁ → dependent-set₀
        (DependentSet.tail D₂' y₁))
      (λ y₁ → dependent-simple-partial-function₀
        (DependentSimplePartialFunction.tail F₂ y₁)))
dependent-simple-partial-function-sigma-sum
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-simple-partial-function-sigma-sum
      (DependentSplitFunctor.tail F₁ x)
      (DependentSimplePartialFunction.tail F₂ x))

