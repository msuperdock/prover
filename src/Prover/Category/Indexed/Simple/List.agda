module Prover.Category.Indexed.Simple.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.List
  using (indexed-category-list)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Prelude

-- ## IndexedSimpleCategory

indexed-simple-category-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
indexed-simple-category-list C'
  = indexed-category-simple
  $ indexed-category-list
    (indexed-category-unit C')

