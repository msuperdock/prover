module Prover.Category.Dependent.Simple.Decidable where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Relation
  using (DependentSimpleRelation)
open import Prover.Prelude

-- ## Types

DependentSimpleDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleRelation C'
  → Set

record DependentSimpleDecidable'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  {C' : DependentSimpleCategory C}
  (R : DependentSimpleRelation C')
  : Set

-- ## Definitions

DependentSimpleDecidable {n = zero}
  = Decidable
DependentSimpleDecidable {n = suc _}
  = DependentSimpleDecidable'

record DependentSimpleDecidable' {_ C} R where

  inductive

  field

    decidable
      : (x : ChainCategory.Object C)
      → DependentSimpleDecidable
        (DependentSimpleRelation.relation R x)

module DependentSimpleDecidable
  = DependentSimpleDecidable'

