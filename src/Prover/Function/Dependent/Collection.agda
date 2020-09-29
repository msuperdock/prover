module Prover.Function.Dependent.Collection where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Relation
  using (DependentRelation)
open import Prover.Prelude

-- ## Types

dependent-set-collection
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → DependentRelation C'
  → DependentSet C

-- ## Definitions

dependent-set-collection {n = zero} R
  = Collection R

dependent-set-collection {n = suc _} R
  = record
  { set
    = λ x → dependent-set-collection
      (DependentRelation.relation R x)
  }

