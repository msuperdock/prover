module Prover.Function.Dependent.Simple.Bool.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Function.Bool.List
  using (bool-function-list)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction; cons; dependent-simple-bool-function₀;
    nil)
open import Prover.Prelude

-- ## DependentSimpleBoolFunction

dependent-simple-bool-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → DependentSimpleBoolFunction C'
  → DependentSimpleBoolFunction
    (dependent-simple-category-list C')
dependent-simple-bool-function-list
  {n = zero} F
  = nil
    (bool-function-list
      (dependent-simple-bool-function₀ F))
dependent-simple-bool-function-list
  {n = suc _} F
  = cons
    (λ x → dependent-simple-bool-function-list
      (DependentSimpleBoolFunction.tail F x))

