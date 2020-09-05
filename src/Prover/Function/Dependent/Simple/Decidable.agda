module Prover.Function.Dependent.Simple.Decidable where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Simple.Relation
  using (DependentSimpleRelation; dependent-simple-relation₀)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data DependentSimpleDecidable
    : {n : ℕ}
    → {C : ChainCategory n}
    → {C' : DependentSet C}
    → DependentSimpleRelation C'
    → Set
    where

    nil
      : {C : ChainCategory zero}
      → {C' : DependentSet C}
      → {R : DependentSimpleRelation C'}
      → Decidable (dependent-simple-relation₀ R)
      → DependentSimpleDecidable R
    
    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSet C}
      → {R : DependentSimpleRelation C'}
      → ((x : ChainCategory.Object C)
        → DependentSimpleDecidable (DependentSimpleRelation.tail R x))
      → DependentSimpleDecidable R

  -- ### Interface

  dependent-simple-decidable₀
    : {C : ChainCategory zero}
    → {C' : DependentSet C}
    → {R : DependentSimpleRelation C'}
    → DependentSimpleDecidable R
    → Decidable (dependent-simple-relation₀ R)
  dependent-simple-decidable₀ (nil d)
    = d

  dependent-simple-decidable-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSet C}
    → {R : DependentSimpleRelation C'}
    → DependentSimpleDecidable R
    → (x : ChainCategory.Object C)
    → DependentSimpleDecidable (DependentSimpleRelation.tail R x)
  dependent-simple-decidable-tail (cons d)
    = d

-- ## Module

DependentSimpleDecidable
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSet C}
  → DependentSimpleRelation C'
  → Set
DependentSimpleDecidable
  = Internal.DependentSimpleDecidable

open Internal public
  using (dependent-simple-decidable₀)

module DependentSimpleDecidable where

  open Internal public using () renaming
    ( dependent-simple-decidable-tail
      to tail
    )

