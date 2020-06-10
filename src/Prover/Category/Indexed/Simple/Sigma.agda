module Prover.Category.Indexed.Simple.Sigma where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Sigma.Maybe
  using (indexed-category-sigma-may)
open import Prover.Category.Indexed.Simple
  using (IndexedSet)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## IndexedSet

indexed-set-sigma
  : {n : ℕ}
  → {C : ChainCategory n}
  → (C₁' : IndexedCategory C)
  → IndexedSet (chain-category-snoc C₁')
  → IndexedSet C
indexed-set-sigma C₁' C₂'
  = indexed-category-simple
  $ indexed-category-sigma-may C₁'
    (indexed-category-unit C₂')

