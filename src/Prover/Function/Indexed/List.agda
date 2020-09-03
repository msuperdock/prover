module Prover.Function.Indexed.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Indexed
  using (IndexedSet; cons; indexed-set₀; nil)
open import Prover.Prelude

-- ## IndexedSet

indexed-set-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSet C
  → IndexedSet C
indexed-set-list
  {n = zero} C'
  = nil
    (List
      (indexed-set₀ C'))
indexed-set-list
  {n = suc _} C'
  = cons
    (λ x → indexed-set-list
      (IndexedSet.tail C' x))

