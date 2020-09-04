module Prover.Function.Dependent.Simple.Split.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction; cons; dependent-simple-split-function₀;
    nil)
open import Prover.Function.Split.List
  using (split-function-list)
open import Prover.Prelude

-- ## DependentSimpleSplitFunction

dependent-simple-split-function-list
  : {A : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleSplitFunction A C'
  → DependentSimpleSplitFunction
    (List A)
    (dependent-simple-category-list C')
dependent-simple-split-function-list
  {n = zero} F
  = nil
    (split-function-list
      (dependent-simple-split-function₀ F))
dependent-simple-split-function-list
  {n = suc _} F
  = cons
    (λ x → dependent-simple-split-function-list
      (DependentSimpleSplitFunction.tail F x))

