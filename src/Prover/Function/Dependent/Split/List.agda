module Prover.Function.Dependent.Split.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.List
  using (dependent-category-list)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; cons; dependent-split-function₀; nil)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

-- ## DependentSplitFunction

dependent-split-function-list
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → DependentSplitFunction A C'
  → DependentSplitFunction
    (List A)
    (dependent-category-list C')
dependent-split-function-list
  {n = zero} F
  = nil
    (split-function-list
      (dependent-split-function₀ F))
dependent-split-function-list
  {n = suc _} F
  = cons
    (λ x → dependent-split-function-list
      (DependentSplitFunction.tail F x))

