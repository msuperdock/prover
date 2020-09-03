module Prover.Function.Indexed.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Indexed
  using (IndexedSet; cons; indexed-set₀; nil)
open import Prover.Prelude

-- ## IndexedSet

indexed-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedSet C
  → IndexedSet C
indexed-set-product
  {n = zero} C₁' C₂'
  = nil
    (_×_
      (indexed-set₀ C₁')
      (indexed-set₀ C₂'))
indexed-set-product
  {n = suc _} C₁' C₂'
  = cons
    (λ x → indexed-set-product
      (IndexedSet.tail C₁' x)
      (IndexedSet.tail C₂' x))

