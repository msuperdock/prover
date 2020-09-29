module Prover.Category.Dependent.Decidable where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Relation
  using (DependentRelation)
open import Prover.Prelude

-- ## Types

DependentDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentRelation C'
  → Set

record DependentDecidable'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  {C' : DependentCategory C}
  (R : DependentRelation C')
  : Set

-- ## Definitions

DependentDecidable {n = zero}
  = Decidable
DependentDecidable {n = suc _}
  = DependentDecidable'

record DependentDecidable' {_ C} R where

  inductive

  field

    decidable
      : (x : ChainCategory.Object C)
      → DependentDecidable
        (DependentRelation.relation R x)

module DependentDecidable
  = DependentDecidable'

