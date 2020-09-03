module Prover.Function.Indexed where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Definition

  data IndexedSet
    : {n : ℕ}
    → ChainCategory n
    → Set₁
    where

    nil
      : {C : ChainCategory zero}
      → Set
      → IndexedSet C

    cons
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → ((x : ChainCategory.Object C)
        → IndexedSet (ChainCategory.tail C x))
      → IndexedSet C

  -- ### Interface

  indexed-set₀
    : {C : ChainCategory zero}
    → IndexedSet C
    → Set
  indexed-set₀ (nil A)
    = A

  indexed-set-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSet C
    → (x : ChainCategory.Object C)
    → IndexedSet (ChainCategory.tail C x)
  indexed-set-tail (cons C')
    = C'

-- ## Module

IndexedSet
  : {n : ℕ}
  → ChainCategory n
  → Set₁
IndexedSet
  = Internal.IndexedSet

open Internal.IndexedSet public

open Internal public
  using (indexed-set₀)

module IndexedSet where

  open Internal public using () renaming
    ( indexed-set-tail
      to tail
    )
  
