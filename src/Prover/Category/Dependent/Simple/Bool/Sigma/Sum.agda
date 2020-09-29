module Prover.Category.Dependent.Simple.Bool.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Bool.Sigma.Sum
  using (bool-function-sigma-sum)
open import Prover.Prelude

-- ## Types

dependent-simple-bool-function-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → {C₂₂' : DependentSimpleCategory (chain-category-snoc C₂₁')}
  → (F₁ : DependentSplitFunctor C₁₁' C₂₁')
  → DependentSimpleBoolFunction C₂₂'
  → DependentSimpleBoolFunction
    (dependent-simple-category-sigma-sum C₂₂' F₁)

-- ## Definitions

dependent-simple-bool-function-sigma-sum {n = zero} {C₂₂' = C₂₂'} _ G₂₂
  = bool-function-sigma-sum
    (DependentSimpleCategory.category C₂₂')
    (DependentSimpleBoolFunction.bool-function G₂₂)

dependent-simple-bool-function-sigma-sum {n = suc _} F₁ G₂₂
  = record
  { function
    = λ x → dependent-simple-bool-function-sigma-sum
      (DependentSplitFunctor.split-functor F₁ x)
      (DependentSimpleBoolFunction.bool-function G₂₂ x)
  }

