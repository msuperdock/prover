module Prover.Category.Dependent.Simple.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Product
  using (dependent-category-product)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Prelude

-- ## DependentSimpleCategory

dependent-simple-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory C
  → DependentSimpleCategory C
dependent-simple-category-product C₁' C₂'
  = dependent-category-simple
  $ dependent-category-product
    (dependent-category-unit C₁')
    (dependent-category-unit C₂')

