module Prover.Category.Indexed.Base where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory)
open import Prover.Prelude

-- ## Internal

module Internal where

  -- ### Types

  -- #### IndexedSet

  data IndexedSet
    : {n : ℕ}
    → ChainCategory n
    → Set₁

  -- #### IndexedDependentSet

  record IndexedDependentSet
    {n : ℕ}
    {C : Category}
    (C' : ChainDependentCategory C n)
    : Set₁

  -- ### Definitions

  -- #### IndexedSet

  data IndexedSet where

    empty
      : {C : ChainCategory zero}
      → Set
      → IndexedSet C

    sigma
      : {n : ℕ}
      → {C : ChainCategory (suc n)}
      → IndexedDependentSet
        (ChainCategory.unpack C)
      → IndexedSet C

  -- #### IndexedDependentSet

  record IndexedDependentSet {_ C} C' where

    inductive

    no-eta-equality

    constructor

      indexed-dependent-set

    field
      
      indexed-set
        : (x : Category.Object C)
        → IndexedSet
          (ChainDependentCategory.chain-category C' x)

  -- ### Interface

  indexed-set₀
    : {C : ChainCategory zero}
    → IndexedSet C
    → Set
  indexed-set₀ (empty A)
    = A

  indexed-set-unpack
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSet C
    → IndexedDependentSet
      (ChainCategory.unpack C)
  indexed-set-unpack (sigma A)
    = A

  indexed-set-tail
    : {n : ℕ}
    → {C : ChainCategory (suc n)}
    → IndexedSet C
    → (x : Category.Object (ChainCategory.head C))
    → IndexedSet (ChainCategory.tail C x)
  indexed-set-tail C'
    = IndexedDependentSet.indexed-set
      (indexed-set-unpack C')

  -- ### Destruction

  indexed-dependent-set₀
    : {C : Category}
    → {C' : ChainDependentCategory C zero}
    → IndexedDependentSet C'
    → Category.Object C
    → Set
  indexed-dependent-set₀ C'' x
    = indexed-set₀
      (IndexedDependentSet.indexed-set C'' x)

-- ## Module

open Internal public
  using (IndexedDependentSet; indexed-dependent-set; indexed-dependent-set₀)

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
    ; indexed-set-unpack
      to unpack
    )

