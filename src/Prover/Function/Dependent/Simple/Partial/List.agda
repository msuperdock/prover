module Prover.Function.Dependent.Simple.Partial.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.List
  using (dependent-set-list)
open import Prover.Function.Dependent.Simple.Partial
  using (DependentSimplePartialFunction; cons;
    dependent-simple-partial-function₀; nil)
open import Prover.Function.Partial.List
  using (partial-function-list)
open import Prover.Prelude

-- ## DependentSimplePartialFunction

dependent-simple-partial-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSet C}
  → DependentSimplePartialFunction C' D'
  → DependentSimplePartialFunction
    (dependent-simple-category-list C')
    (dependent-set-list D')
dependent-simple-partial-function-list
  {n = zero} F
  = nil
    (partial-function-list
      (dependent-simple-partial-function₀ F))
dependent-simple-partial-function-list
  {n = suc _} F
  = cons
    (λ x → dependent-simple-partial-function-list
      (DependentSimplePartialFunction.tail F x))

