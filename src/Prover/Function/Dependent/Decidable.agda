module Prover.Function.Dependent.Decidable where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Relation
  using (DependentRelation)
open import Prover.Prelude

-- ## Types

DependentDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → DependentRelation C'
  → Set

record DependentDecidable'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  {C' : DependentSet C}
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

