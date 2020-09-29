module Prover.Category.Dependent.Simple.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Sigma.Sum
  using (dependent-category-sigma-sum)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## DependentSimpleCategory

dependent-simple-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁₁' C₂₁' : DependentCategory C}
  → DependentSimpleCategory (chain-category-snoc C₂₁')
  → DependentSplitFunctor C₁₁' C₂₁'
  → DependentSimpleCategory C
dependent-simple-category-sigma-sum C₂₂' F₁
  = dependent-category-simple
  $ dependent-category-sigma-sum
    (dependent-category-unit C₂₂') F₁

