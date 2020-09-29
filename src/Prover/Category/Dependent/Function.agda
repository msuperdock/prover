module Prover.Category.Dependent.Function where

open import Prover.Category
  using (Category)
open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Prelude

-- ## Types

DependentFunction
  : {n : ℕ}
  → {C : ChainCategory n}
  → DependentCategory C
  → Set
  → Set

record DependentFunction'
  {n : ℕ}
  {C : ChainCategory (suc n)}
  (C' : DependentCategory C)
  (A : Set)
  : Set

-- ## Definitions

DependentFunction {n = zero} C' A
  = Category.Object C' → A
DependentFunction {n = suc _} C' A
  = DependentFunction' C' A

record DependentFunction' {_ C} C' A where

  inductive

  field

    function
      : (x : ChainCategory.Object C)
      → DependentFunction
        (DependentCategory.category C' x) A

module DependentFunction
  = DependentFunction'

-- ## Compose

dependent-function-compose
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C' : DependentCategory C}
  → {A B : Set}
  → (A → B)
  → DependentFunction C' A
  → DependentFunction C' B

dependent-function-compose {n = zero} f g
  = f ∘ g

dependent-function-compose {n = suc _} f G
  = record
  { function
    = λ x → dependent-function-compose f
      (DependentFunction.function G x)
  }

