module Prover.Category.Indexed.Simple.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Product
  using (indexed-category-product)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Prelude

-- ## IndexedSimpleCategory

indexed-simple-category-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
indexed-simple-category-product C₁' C₂'
  = indexed-category-simple
  $ indexed-category-product
    (indexed-category-unit C₁')
    (indexed-category-unit C₂')

