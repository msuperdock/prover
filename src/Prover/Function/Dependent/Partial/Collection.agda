module Prover.Function.Dependent.Partial.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Collection
  using (dependent-set-collection)
open import Prover.Function.Dependent.Decidable
  using (DependentDecidable)
open import Prover.Function.Dependent.List
  using (dependent-set-list)
open import Prover.Function.Dependent.Partial
  using (DependentPartialFunction)
open import Prover.Function.Dependent.Relation
  using (DependentRelation)
open import Prover.Function.Partial.Collection
  using (partial-function-collection)
open import Prover.Prelude

-- ## Types

dependent-partial-function-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → {R : DependentRelation C'}
  → DependentDecidable R
  → DependentPartialFunction
    (dependent-set-list C')
    (dependent-set-collection R)

-- ## Definitions

dependent-partial-function-collection {n = zero} {R = R} d
  = partial-function-collection R d

dependent-partial-function-collection {n = suc _} d
  = record
  { partial-function
    = λ x → dependent-partial-function-collection
      (DependentDecidable.decidable d x)
  }

