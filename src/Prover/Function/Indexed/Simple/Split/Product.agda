module Prover.Function.Indexed.Simple.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Function.Indexed.Simple.Split
  using (IndexedSimpleSplitFunction; empty; indexed-simple-split-function₀;
    sigma)
open import Prover.Function.Split.Product
  using (split-function-product)
open import Prover.Prelude

-- ## IndexedSimpleSplitFunction

indexed-simple-split-function-product
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedSimpleCategory C}
  → IndexedSimpleSplitFunction A₁ C₁'
  → IndexedSimpleSplitFunction A₂ C₂'
  → IndexedSimpleSplitFunction
    (A₁ × A₂)
    (indexed-simple-category-product C₁' C₂')
indexed-simple-split-function-product {n = zero} F₁ F₂
  = empty
    (split-function-product
      (indexed-simple-split-function₀ F₁)
      (indexed-simple-split-function₀ F₂))
indexed-simple-split-function-product {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-simple-split-function-product 
      (IndexedSimpleSplitFunction.tail F₁ x)
      (IndexedSimpleSplitFunction.tail F₂ x))

