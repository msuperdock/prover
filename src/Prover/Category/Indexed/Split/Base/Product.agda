module Prover.Category.Indexed.Split.Base.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.Product
  using (indexed-category-product)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Category.Indexed.Split.Base
  using (IndexedSimpleSplitFunction; IndexedSplitFunction; empty;
    indexed-simple-split-function₀; indexed-split-function₀; sigma)
open import Prover.Category.Split.Base.Product
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

