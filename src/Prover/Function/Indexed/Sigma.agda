module Prover.Function.Indexed.Sigma where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory; indexed-category₀)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Function.Indexed
  using (IndexedSet; cons; indexed-set₀; nil)
open import Prover.Prelude

-- ## IndexedSet

indexed-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : IndexedCategory C)
  → IndexedSet (chain-category-snoc C₁')
  → IndexedSet C
indexed-set-sigma
  {n = zero} C₁' C₂'
  = nil
    (Σ
      (Category.Object
        (indexed-category₀ C₁'))
      (λ x → indexed-set₀
        (IndexedSet.tail C₂' x)))
indexed-set-sigma
  {n = suc _} C₁' C₂'
  = cons
    (λ x → indexed-set-sigma
      (IndexedCategory.tail C₁' x)
      (IndexedSet.tail C₂' x))

