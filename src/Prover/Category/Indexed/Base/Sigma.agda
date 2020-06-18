module Prover.Category.Indexed.Base.Sigma where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory; ChainDependentCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; IndexedDependentCategory; indexed-category₀)
open import Prover.Category.Indexed.Base
  using (IndexedDependentSet; IndexedSet; empty; indexed-dependent-set;
    indexed-dependent-set₀; sigma)
open import Prover.Category.Snoc
  using (chain-category-snoc; chain-dependent-category-snoc)
open import Prover.Prelude

-- ## Prelude

set-sigma
  : (A₁ : Set)
  → (A₁ → Set)
  → Set
set-sigma
  = Σ

-- ## Types

-- ### IndexedSet

indexed-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : IndexedCategory C)
  → IndexedSet (chain-category-snoc C₁')
  → IndexedSet C

-- ### IndexedDependentSet

indexed-dependent-set-sigma
  : {n : ℕ}
  → {C : Category}
  → {C' : ChainDependentCategory C n}
  → (C₁'' : IndexedDependentCategory C')
  → IndexedDependentSet (chain-dependent-category-snoc C₁'')
  → IndexedDependentSet C'

-- ## Definitions

-- ### IndexedSet

indexed-set-sigma {n = zero} C₁' C₂'
  = empty
    (set-sigma
      (Category.Object
        (indexed-category₀ C₁'))
      (indexed-dependent-set₀
        (IndexedSet.unpack C₂')))
indexed-set-sigma {n = suc _} C₁'' C₂''
  = sigma
    (indexed-dependent-set-sigma
      (IndexedCategory.unpack C₁'')
      (IndexedSet.unpack C₂''))

-- ### IndexedDependentSet

indexed-dependent-set-sigma C₁'' C₂''
  = indexed-dependent-set
    (λ x → indexed-set-sigma
      (IndexedDependentCategory.indexed-category C₁'' x)
      (IndexedDependentSet.indexed-set C₂'' x))

