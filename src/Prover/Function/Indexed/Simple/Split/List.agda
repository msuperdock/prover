module Prover.Function.Indexed.Simple.Split.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed.Simple
  using (IndexedSimpleCategory)
open import Prover.Category.Indexed.Simple.List
  using (indexed-simple-category-list)
open import Prover.Function.Indexed.Simple.Split
  using (IndexedSimpleSplitFunction; empty; indexed-simple-split-function₀;
    sigma)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

-- ## IndexedSimpleSplitFunction

indexed-simple-split-function-list
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedSimpleCategory C}
  → IndexedSimpleSplitFunction A C'
  → IndexedSimpleSplitFunction
    (List A)
    (indexed-simple-category-list C')
indexed-simple-split-function-list {n = zero} F
  = empty
    (split-function-list
      (indexed-simple-split-function₀ F))
indexed-simple-split-function-list {n = suc _} F
  = sigma
    (λ x → indexed-simple-split-function-list
      (IndexedSimpleSplitFunction.tail F x))

