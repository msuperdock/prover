module Prover.Function.Indexed.Simple.Bool.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Function.Bool.Product
  using (bool-function-product)
open import Prover.Function.Indexed.Simple.Bool
  using (IndexedSimpleBoolFunction; empty; indexed-simple-bool-function₀; sigma)
open import Prover.Prelude

-- ## IndexedSimpleBoolFunction

indexed-simple-bool-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedSimpleCategory C}
  → IndexedSimpleBoolFunction C₁'
  → IndexedSimpleBoolFunction C₂'
  → IndexedSimpleBoolFunction
    (indexed-simple-category-product C₁' C₂')
indexed-simple-bool-function-product {n = zero} F₁ F₂
  = empty
    (bool-function-product
      (indexed-simple-bool-function₀ F₁)
      (indexed-simple-bool-function₀ F₂))
indexed-simple-bool-function-product {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-simple-bool-function-product
      (IndexedSimpleBoolFunction.tail F₁ x)
      (IndexedSimpleBoolFunction.tail F₂ x))

