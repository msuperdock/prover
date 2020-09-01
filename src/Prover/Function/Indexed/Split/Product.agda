module Prover.Function.Indexed.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Product
  using (indexed-category-product)
open import Prover.Function.Indexed.Split
  using (IndexedSplitFunction; empty; indexed-split-function₀; sigma)
open import Prover.Function.Split.Product
  using (split-function-product)
open import Prover.Prelude

-- ## IndexedSplitFunction

indexed-split-function-product
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedCategory C}
  → IndexedSplitFunction A₁ C₁'
  → IndexedSplitFunction A₂ C₂'
  → IndexedSplitFunction
    (A₁ × A₂)
    (indexed-category-product C₁' C₂')
indexed-split-function-product {n = zero} F₁ F₂
  = empty
    (split-function-product
      (indexed-split-function₀ F₁)
      (indexed-split-function₀ F₂))
indexed-split-function-product {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-split-function-product 
      (IndexedSplitFunction.tail F₁ x)
      (IndexedSplitFunction.tail F₂ x))

