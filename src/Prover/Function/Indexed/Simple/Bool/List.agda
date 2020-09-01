module Prover.Function.Indexed.Simple.Bool.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.List
  using (indexed-simple-category-list)
open import Prover.Function.Bool.List
  using (bool-function-list)
open import Prover.Function.Indexed.Simple.Bool
  using (IndexedSimpleBoolFunction; empty; indexed-simple-bool-function₀; sigma)
open import Prover.Prelude

-- ## IndexedSimpleBoolFunction

indexed-simple-bool-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → IndexedSimpleBoolFunction C'
  → IndexedSimpleBoolFunction
    (indexed-simple-category-list C')
indexed-simple-bool-function-list {n = zero} F
  = empty
    (bool-function-list
      (indexed-simple-bool-function₀ F))
indexed-simple-bool-function-list {n = suc _} F
  = sigma
    (λ x → indexed-simple-bool-function-list
      (IndexedSimpleBoolFunction.tail F x))

