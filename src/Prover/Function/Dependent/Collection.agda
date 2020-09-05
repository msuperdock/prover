module Prover.Function.Dependent.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet; cons; nil)
open import Prover.Function.Dependent.Simple.Relation
  using (DependentSimpleRelation; dependent-simple-relation₀)
open import Prover.Prelude

-- ## DependentSet

dependent-set-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → DependentSimpleRelation C'
  → DependentSet C
dependent-set-collection
  {n = zero} R
  = nil
    (Collection
      (dependent-simple-relation₀ R))
dependent-set-collection
  {n = suc _} R
  = cons
    (λ x → dependent-set-collection
      (DependentSimpleRelation.tail R x))

