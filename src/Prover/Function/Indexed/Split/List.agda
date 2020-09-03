module Prover.Function.Indexed.Split.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Indexed
  using (IndexedCategory)
open import Prover.Category.Indexed.List
  using (indexed-category-list)
open import Prover.Function.Indexed.Split
  using (IndexedSplitFunction; cons; indexed-split-function₀; nil)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

-- ## IndexedSplitFunction

indexed-split-function-list
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : IndexedCategory C}
  → IndexedSplitFunction A C'
  → IndexedSplitFunction
    (List A)
    (indexed-category-list C')
indexed-split-function-list
  {n = zero} F
  = nil
    (split-function-list
      (indexed-split-function₀ F))
indexed-split-function-list
  {n = suc _} F
  = cons
    (λ x → indexed-split-function-list
      (IndexedSplitFunction.tail F x))

