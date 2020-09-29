module Prover.Category.Dependent.Simple.Split.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Sigma
  using (dependent-simple-category-sigma)
open import Prover.Category.Dependent.Simple.Sigma.Sum
  using (dependent-simple-category-sigma-sum)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Prover.Category.Dependent.Simple.Split.Convert
  using (dependent-split-functor-simple)
open import Prover.Category.Dependent.Split
  using (DependentSplitFunctor)
open import Prover.Category.Dependent.Split.Sigma.Sum
  using (dependent-split-functor-sigma-sum)
open import Prover.Category.Dependent.Split.Unit
  using (dependent-split-functor-unit)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## DependentSimpleSplitFunctor

dependent-simple-split-functor-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : DependentCategory C}
  → {C₂' D₂' : DependentSimpleCategory (chain-category-snoc D₁')}
  → (F₁ : DependentSplitFunctor C₁' D₁')
  → DependentSimpleSplitFunctor C₂' D₂'
  → DependentSimpleSplitFunctor
    (dependent-simple-category-sigma-sum C₂' F₁)
    (dependent-simple-category-sigma D₁' D₂')
dependent-simple-split-functor-sigma-sum F₁ F₂
  = dependent-split-functor-simple
  $ dependent-split-functor-sigma-sum F₁
    (dependent-split-functor-unit F₂)

