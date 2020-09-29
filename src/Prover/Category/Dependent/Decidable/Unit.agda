module Prover.Category.Dependent.Decidable.Unit where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Decidable
  using (DependentDecidable)
open import Prover.Category.Dependent.Relation.Unit
  using (dependent-relation-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Decidable
  using (DependentSimpleDecidable)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Prelude

-- ## Types

dependent-decidable-unit
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → (R : DependentSimpleRelation C')
  → DependentSimpleDecidable R
  → DependentDecidable
    (dependent-relation-unit R)

-- ## Definitions

dependent-decidable-unit {n = zero} _ d
  = d

dependent-decidable-unit {n = suc _} R d
  = record
  { decidable
    = λ x → dependent-decidable-unit
      (DependentSimpleRelation.relation R x)
      (DependentSimpleDecidable.decidable d x)
  }

