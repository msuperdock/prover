module Prover.Function.Indexed.Product where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory)
open import Prover.Function.Indexed
  using (IndexedDependentSet; IndexedSet; empty; indexed-dependent-set;
    indexed-set₀; sigma)
open import Prover.Prelude

-- ## Prelude

set-product
  : Set
  → Set
  → Set
set-product A₁ A₂
  = A₁ × A₂

-- ## Types

-- ### IndexedSet

indexed-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedSet C
  → IndexedSet C

-- ### IndexedDependentSet

indexed-dependent-set-product
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentSet C'
  → IndexedDependentSet C'
  → IndexedDependentSet C'

-- ## Definitions

-- ### IndexedSet

indexed-set-product {n = zero} C₁' C₂'
  = empty
    (set-product
      (indexed-set₀ C₁')
      (indexed-set₀ C₂'))
indexed-set-product {n = suc _} C₁' C₂'
  = sigma
    (indexed-dependent-set-product
      (IndexedSet.unpack C₁')
      (IndexedSet.unpack C₂'))

-- ### IndexedDependentSet

indexed-dependent-set-product C₁'' C₂''
  = indexed-dependent-set
    (λ x → indexed-set-product
      (IndexedDependentSet.indexed-set C₁'' x)
      (IndexedDependentSet.indexed-set C₂'' x))

