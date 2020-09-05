module Prover.Function.Dependent.Simple.Partial.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Collection
  using (dependent-set-collection)
open import Prover.Function.Dependent.List
  using (dependent-set-list)
open import Prover.Function.Dependent.Simple.Decidable
  using (DependentSimpleDecidable; dependent-simple-decidable₀)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction'; cons; nil)
open import Prover.Function.Dependent.Simple.Relation
  using (DependentSimpleRelation; dependent-simple-relation₀)
open import Prover.Function.Partial.Collection
  using (partial-function-collection)
open import Prover.Prelude

-- ## DependentSimplePartialFunction'

dependent-simple-partial-function-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → {R : DependentSimpleRelation C'}
  → DependentSimpleDecidable R
  → DependentSimplePartialFunction'
    (dependent-set-list C')
    (dependent-set-collection R)
dependent-simple-partial-function-collection
  {n = zero} {R = R} d
  = nil
    (partial-function-collection
      (dependent-simple-relation₀ R)
      (dependent-simple-decidable₀ d))
dependent-simple-partial-function-collection
  {n = suc _} d
  = cons
    (λ x → dependent-simple-partial-function-collection
      (DependentSimpleDecidable.tail d x))

