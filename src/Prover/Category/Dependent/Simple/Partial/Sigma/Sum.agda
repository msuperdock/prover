module Prover.Category.Dependent.Simple.Partial.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Sigma
  using (dependent-set-sigma)
open import Prover.Function.Partial.Sigma.Sum
  using (partial-function-sigma-sum)
open import Prover.Prelude

-- ## Types

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

-- ## Definitions

dependent-simple-partial-function-sigma-sum {n = zero}
  {C₂' = C₂'} {D₂' = D₂'} _ F₂
  = partial-function-sigma-sum
    (DependentSimpleCategory.category C₂')
    (DependentSet.set D₂')
    (DependentSimplePartialFunction.partial-function F₂)

dependent-simple-partial-function-sigma-sum {n = suc _} F₁ F₂
  = record
  { partial-function
    = λ x → dependent-simple-partial-function-sigma-sum
      (DependentSplitFunctor.split-functor F₁ x)
      (DependentSimplePartialFunction.partial-function F₂ x)
  }

