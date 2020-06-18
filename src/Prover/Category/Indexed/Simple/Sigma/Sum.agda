module Prover.Category.Indexed.Simple.Sigma.Sum where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Sigma.Sum
  using (indexed-category-sigma-sum)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Split
  using (IndexedSplitFunctor)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Category.Snoc
  using (chain-category-snoc)
open import Prover.Prelude

-- ## IndexedSimpleCategory

indexed-simple-category-sigma-sum
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' D₁' : IndexedCategory C}
  → IndexedSimpleCategory (chain-category-snoc D₁')
  → IndexedSplitFunctor C₁' D₁'
  → IndexedSimpleCategory C
indexed-simple-category-sigma-sum C₂' F₁
  = indexed-category-simple
  $ indexed-category-sigma-sum
    (indexed-category-unit C₂') F₁

