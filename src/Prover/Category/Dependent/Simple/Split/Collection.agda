module Prover.Category.Dependent.Simple.Split.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Decidable.Unit
  using (dependent-decidable-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Collection
  using (dependent-simple-category-collection)
open import Prover.Category.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Category.Dependent.Simple.Split
  using (DependentSimpleSplitFunctor)
open import Prover.Category.Dependent.Simple.Split.Convert
  using (dependent-split-functor-simple)
open import Prover.Category.Dependent.Split.Collection
  using (dependent-split-functor-collection)
open import Prover.Prelude

-- ## DependentSimpleSplitFunctor

dependent-simple-split-functor-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentSimpleSplitFunctor
    (dependent-simple-category-list C')
    (dependent-simple-category-collection R)
dependent-simple-split-functor-collection {R = R} d
  = dependent-split-functor-simple
  $ dependent-split-functor-collection
    (dependent-decidable-unit R d)

