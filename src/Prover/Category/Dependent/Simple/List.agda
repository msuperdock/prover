module Prover.Category.Dependent.Simple.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.List
  using (dependent-category-list)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Unit
  using (dependent-category-unit)
open import Prover.Prelude

-- ## DependentSimpleCategory

dependent-simple-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSimpleCategory C
dependent-simple-category-list C'
  = dependent-category-simple
  $ dependent-category-list
    (dependent-category-unit C')

