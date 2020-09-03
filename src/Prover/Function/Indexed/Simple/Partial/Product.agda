module Prover.Function.Indexed.Simple.Partial.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.Product
  using (indexed-simple-category-product)
open import Prover.Function.Indexed
  using (IndexedSet)
open import Prover.Function.Indexed.Product
  using (indexed-set-product)
open import Prover.Function.Indexed.Simple.Partial
  using (IndexedSimplePartialFunction; cons; indexed-simple-partial-function₀;
    nil)
open import Prover.Function.Partial.Product
  using (partial-function-product)
open import Prover.Prelude

-- ## IndexedSimplePartialFunction

indexed-simple-partial-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : IndexedSimpleCategory C}
  → {D₁' D₂' : IndexedSet C}
  → IndexedSimplePartialFunction C₁' D₁'
  → IndexedSimplePartialFunction C₂' D₂'
  → IndexedSimplePartialFunction
    (indexed-simple-category-product C₁' C₂')
    (indexed-set-product D₁' D₂')
indexed-simple-partial-function-product
  {n = zero} F₁ F₂
  = nil
    (partial-function-product
      (indexed-simple-partial-function₀ F₁)
      (indexed-simple-partial-function₀ F₂))
indexed-simple-partial-function-product
  {n = suc _} F₁ F₂
  = cons
    (λ x → indexed-simple-partial-function-product
      (IndexedSimplePartialFunction.tail F₁ x)
      (IndexedSimplePartialFunction.tail F₂ x))

