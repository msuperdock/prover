module Prover.Function.Indexed.Partial.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Function.Indexed
  using (IndexedSet)
open import Prover.Function.Indexed.Partial
  using (IndexedPartialFunction; empty; indexed-partial-function₀; sigma)
open import Prover.Function.Indexed.Product
  using (indexed-set-product)
open import Prover.Function.Partial.Product
  using (partial-function-product)
open import Prover.Prelude

-- ## IndexedPartialFunction

indexed-partial-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedSimpleCategory C}
  → {D₁' D₂' : IndexedSet C}
  → IndexedPartialFunction C₁' D₁'
  → IndexedPartialFunction C₂' D₂'
  → IndexedPartialFunction
    (indexed-simple-category-product C₁' C₂')
    (indexed-set-product D₁' D₂')
indexed-partial-function-product {n = zero} F₁ F₂
  = empty
    (partial-function-product
      (indexed-partial-function₀ F₁)
      (indexed-partial-function₀ F₂))
indexed-partial-function-product {n = suc _} F₁ F₂
  = sigma
    (λ x → indexed-partial-function-product
      (IndexedPartialFunction.tail F₁ x)
      (IndexedPartialFunction.tail F₂ x))

