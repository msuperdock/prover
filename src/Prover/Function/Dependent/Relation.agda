module Prover.Function.Dependent.Relation where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Prelude

-- ## Types

DependentRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → Set₁

record DependentRelation'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSet C)
  : Set₁

-- ## Definitions

DependentRelation {n = zero} C'
  = Relation C'
DependentRelation {n = suc _} C'
  = DependentRelation' C'

record DependentRelation' {_ C} C' where

  inductive

  no-eta-equality

  field

    relation
      : (x : ChainCategory.Object C)
      → DependentRelation
        (DependentSet.set C' x)

module DependentRelation
  = DependentRelation'

