module Prover.Function.Dependent.Decidable where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Function.Dependent.Relation
  using (DependentRelation; dependent-relation₀)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data DependentDecidable
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentCategory C}
    → DependentRelation C'
    → Set
    where

    nil
      : {C : ChainCategory zero}
      → {C' : DependentCategory C}
      → {R : DependentRelation C'}
      → Decidable (dependent-relation₀ R)
      → DependentDecidable R
    
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentCategory C}
      → {R : DependentRelation C'}
      → ((x : ChainCategory.Object C)
        → DependentDecidable (DependentRelation.tail R x))
      → DependentDecidable R

  -- ## Interface

  dependent-decidable₀
    : {C : ChainCategory zero}
    → {C' : DependentCategory C}
    → {R : DependentRelation C'}
    → DependentDecidable R
    → Decidable (dependent-relation₀ R)
  dependent-decidable₀ (nil d)
    = d

  dependent-decidable-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentCategory C}
    → {R : DependentRelation C'}
    → DependentDecidable R
    → (x : ChainCategory.Object C)
    → DependentDecidable (DependentRelation.tail R x)
  dependent-decidable-tail (cons d)
    = d

-- ## Module

DependentDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentRelation C'
  → Set
DependentDecidable
  = Internal.DependentDecidable

open Internal public
  using (dependent-decidable₀)

module DependentDecidable where

  open Internal public using () renaming
    ( dependent-decidable-tail
      to tail
    )

