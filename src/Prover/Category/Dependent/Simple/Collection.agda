module Prover.Category.Dependent.Simple.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Collection
  using (dependent-category-collection)
open import Prover.Category.Dependent.Relation.Unit
  using (dependent-relation-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Convert
  using (dependent-category-simple)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Prelude

-- ## DependentSimpleCategory

dependent-simple-category-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleRelation C'
  → DependentSimpleCategory C
dependent-simple-category-collection R
  = dependent-category-simple
  $ dependent-category-collection
    (dependent-relation-unit R)

