module Prover.Category.Indexed.Simple.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Product
  using (indexed-category-product)
open import Prover.Category.Indexed.Simple
  using (IndexedPartialFunction; IndexedSimpleCategory; empty;
    indexed-partial-function₀; sigma)
open import Prover.Category.Indexed.Simple.Convert
  using (indexed-category-simple)
open import Prover.Category.Indexed.Unit
  using (indexed-category-unit)
open import Prover.Category.Partial.Base.Product
  using (partial-function-product)
open import Prover.Prelude

-- ## IndexedSimpleCategory

indexed-set-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
  → IndexedSimpleCategory C
indexed-set-product C₁' C₂'
  = indexed-category-simple
  $ indexed-category-product
    (indexed-category-unit C₁')
    (indexed-category-unit C₂')

-- ## IndexedPartialFunction

indexed-partial-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' D₁' D₂' : IndexedSimpleCategory C}
  → IndexedPartialFunction C₁' D₁'
  → IndexedPartialFunction C₂' D₂'
  → IndexedPartialFunction
    (indexed-set-product C₁' C₂')
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

