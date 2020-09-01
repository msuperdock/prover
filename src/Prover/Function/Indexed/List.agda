module Prover.Function.Indexed.List where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory)
open import Prover.Function.Indexed
  using (IndexedDependentSet; IndexedSet; empty; indexed-dependent-set;
    indexed-set₀; sigma)
open import Prover.Prelude

-- ## Prelude

set-list
  : Set
  → Set
set-list
  = List

-- ## Types

-- ### IndexedSet

indexed-set-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedSet C

-- ### IndexedDependentSet

indexed-dependent-set-list
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → IndexedDependentSet C'
  → IndexedDependentSet C'

-- ## Definitions

-- ### IndexedSet

indexed-set-list {n = zero} C'
  = empty
    (set-list
      (indexed-set₀ C'))
indexed-set-list {n = suc _} C'
  = sigma
    (indexed-dependent-set-list
      (IndexedSet.unpack C'))

-- ### IndexedDependentSet

indexed-dependent-set-list C'
  = indexed-dependent-set
    (λ x → indexed-set-list
      (IndexedDependentSet.indexed-set C' x))

