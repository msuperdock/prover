module Prover.Function.Indexed.Simple.Partial.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.List
  using (indexed-simple-category-list)
open import Prover.Function.Indexed
  using (IndexedSet)
open import Prover.Function.Indexed.List
  using (indexed-set-list)
open import Prover.Function.Indexed.Simple.Partial
  using (IndexedSimplePartialFunction; empty; indexed-simple-partial-function₀;
    sigma)
open import Prover.Function.Partial.List
  using (partial-function-list)
open import Prover.Prelude

-- ## IndexedSimplePartialFunction

indexed-simple-partial-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → {D' : IndexedSet C}
  → IndexedSimplePartialFunction C' D'
  → IndexedSimplePartialFunction
    (indexed-simple-category-list C')
    (indexed-set-list D')
indexed-simple-partial-function-list {n = zero} F
  = empty
    (partial-function-list
      (indexed-simple-partial-function₀ F))
indexed-simple-partial-function-list {n = suc _} F
  = sigma
    (λ x → indexed-simple-partial-function-list
      (IndexedSimplePartialFunction.tail F x))

