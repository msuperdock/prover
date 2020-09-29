module Prover.Category.Dependent.Simple.Partial where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Partial
  using (DependentPartialFunction)
open import Prover.Function.Partial
  using (PartialFunction)
open import Prover.Function.Partial.Compose
  using (partial-function-compose)
open import Prover.Prelude

-- ## Types

DependentSimplePartialFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → DependentSet C
  → Set

record DependentSimplePartialFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  (D' : DependentSet C)
  : Set

-- ## Definitions

DependentSimplePartialFunction {n = zero}
  = PartialFunction
DependentSimplePartialFunction {n = suc _}
  = DependentSimplePartialFunction'

record DependentSimplePartialFunction' {_ C} C' D' where

  inductive

  field

    partial-function
      : (x : ChainCategory.Object C)
      → DependentSimplePartialFunction
        (DependentSimpleCategory.category C' x)
        (DependentSet.set D' x)

module DependentSimplePartialFunction
  = DependentSimplePartialFunction'

-- ## Conversion

dependent-simple-partial-function-bool
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' : DependentSet C}
  → DependentSimplePartialFunction C' D'
  → DependentSimpleBoolFunction C'

dependent-simple-partial-function-bool {n = zero} F
  = PartialFunction.bool-function F

dependent-simple-partial-function-bool {n = suc _} F
  = record
  { function
    = λ x → dependent-simple-partial-function-bool
      (DependentSimplePartialFunction.partial-function F x)
  }

-- ## Compose

dependent-simple-partial-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {D' E' : DependentSet C}
  → DependentPartialFunction D' E'
  → DependentSimplePartialFunction C' D'
  → DependentSimplePartialFunction C' E'

dependent-simple-partial-function-compose {n = zero} F G
  = partial-function-compose F G

dependent-simple-partial-function-compose {n = suc _} F G
  = record
  { partial-function
    = λ x → dependent-simple-partial-function-compose
      (DependentPartialFunction.partial-function F x)
      (DependentSimplePartialFunction.partial-function G x)
  }

