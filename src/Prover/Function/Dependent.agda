module Prover.Function.Dependent where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data DependentSet
    : {n : ℕ}
    → ChainCategory n
    → Set₁
    where

    nil
      : {C : ChainCategory zero}
      → Set
      → DependentSet C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → ((x : ChainCategory.Object C)
        → DependentSet (ChainCategory.tail C x))
      → DependentSet C

  -- ### Interface

  dependent-set₀
    : {C : ChainCategory zero}
    → DependentSet C
    → Set
  dependent-set₀ (nil A)
    = A

  dependent-set-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → DependentSet C
    → (x : ChainCategory.Object C)
    → DependentSet (ChainCategory.tail C x)
  dependent-set-tail (cons C')
    = C'

-- ## Module

DependentSet
  : {n : ℕ}
  → ChainCategory n
  → Set₁
DependentSet
  = Internal.DependentSet

open Internal.DependentSet public

open Internal public
  using (dependent-set₀)

module DependentSet where

  open Internal public using () renaming
    ( dependent-set-tail
      to tail
    )
  
