module Prover.Category.Dependent.Simple.Partial.List where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.List
  using (dependent-simple-category-list)
open import Prover.Category.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.List
  using (dependent-set-list)
open import Prover.Function.Partial.List
  using (partial-function-list)
open import Prover.Prelude

-- ## Types

dependent-simple-partial-function-list
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSet C}
  → DependentSimplePartialFunction C' D'
  → DependentSimplePartialFunction
    (dependent-simple-category-list C')
    (dependent-set-list D')

-- ## Definitions

dependent-simple-partial-function-list {n = zero} F
  = partial-function-list F

dependent-simple-partial-function-list {n = suc _} F
  = record
  { partial-function
    = λ x → dependent-simple-partial-function-list
      (DependentSimplePartialFunction.partial-function F x)
  }

