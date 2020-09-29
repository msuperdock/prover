module Prover.Category.Dependent.Simple.Function where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Prelude

-- ## Types

DependentSimpleFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentSimpleCategory C
  → Set
  → Set

record DependentSimpleFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentSimpleCategory C)
  (A : Set)
  : Set

-- ## Definitions

DependentSimpleFunction {n = zero} C' A
  = C' → A
DependentSimpleFunction {n = suc _} C' A
  = DependentSimpleFunction' C' A

record DependentSimpleFunction' {_ C} C' A where

  inductive

  field

    function
      : (x : ChainCategory.Object C)
      → DependentSimpleFunction
        (DependentSimpleCategory.category C' x) A

module DependentSimpleFunction
  = DependentSimpleFunction'

-- ## Compose

dependent-simple-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentSimpleCategory C}
  → {A B : Set}
  → (A → B)
  → DependentSimpleFunction C' A
  → DependentSimpleFunction C' B

dependent-simple-function-compose {n = zero} f g
  = f ∘ g

dependent-simple-function-compose {n = suc _} f G
  = record
  { function
    = λ x → dependent-simple-function-compose f
      (DependentSimpleFunction.function G x)
  }

