module Prover.Category.Dependent.Simple.Sigma where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Sigma.Maybe
  using (dependent-category-sigma-maybe)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## DependentSimpleCategory

dependent-simple-category-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : DependentCategory C)
  → DependentSimpleCategory (chain-category-snoc C₁')
  → DependentSimpleCategory C
dependent-simple-category-sigma C₁' C₂'
  = dependent-category-simple
  $ dependent-category-sigma-maybe C₁'
    (dependent-category-unit C₂')

