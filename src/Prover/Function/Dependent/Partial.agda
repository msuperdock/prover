module Prover.Function.Dependent.Partial where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Prelude

-- ## Types

DependentPartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSet C
  → DependentSet C
  → Set

record DependentPartialFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' D' : DependentSet C)
  : Set

-- ## Definitions

DependentPartialFunction {n = zero}
  = PartialFunction
DependentPartialFunction {n = suc _}
  = DependentPartialFunction'

record DependentPartialFunction' {_ C} C' D' where

  inductive

  field

    partial-function
      : (x : ChainCategory.Object C)
      → DependentPartialFunction
        (DependentSet.set C' x)
        (DependentSet.set D' x)

module DependentPartialFunction
  = DependentPartialFunction'

