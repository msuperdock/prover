module Prover.Function.Dependent.Simple.Relation where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet; dependent-set₀)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data DependentSimpleRelation
    : {n : ℕ}
    → {C : ChainCategory n}
    → DependentSet C
    → Set₁
    where

    nil
      : {C : ChainCategory zero}
      → {C' : DependentSet C}
      → Relation (dependent-set₀ C')
      → DependentSimpleRelation C'

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → {C' : DependentSet C}
      → ((x : ChainCategory.Object C)
        → DependentSimpleRelation (DependentSet.tail C' x))
      → DependentSimpleRelation C'

  -- ### Interface

  dependent-simple-relation₀
    : {C : ChainCategory zero}
    → {C' : DependentSet C}
    → DependentSimpleRelation C'
    → Relation (dependent-set₀ C')
  dependent-simple-relation₀ (nil R)
    = R

  dependent-simple-relation-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → {C' : DependentSet C}
    → DependentSimpleRelation C'
    → (x : ChainCategory.Object C)
    → DependentSimpleRelation (DependentSet.tail C' x)
  dependent-simple-relation-tail (cons R)
    = R

-- ## Module

DependentSimpleRelation
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → Set₁
DependentSimpleRelation
  = Internal.DependentSimpleRelation

open Internal public
  using (dependent-simple-relation₀)

module DependentSimpleRelation where

  open Internal public using () renaming
    ( dependent-simple-relation-tail
      to tail
    )

