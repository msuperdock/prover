module Prover.Category.Dependent.Simple.Bool.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Function.Bool.Product
  using (bool-function-product)
open import Prover.Prelude

-- ## Types

dependent-simple-bool-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → DependentSimpleBoolFunction C₁'
  → DependentSimpleBoolFunction C₂'
  → DependentSimpleBoolFunction
    (dependent-simple-category-product C₁' C₂')

-- ## Definitions

dependent-simple-bool-function-product {n = zero} F₁ F₂
  = bool-function-product F₁ F₂

dependent-simple-bool-function-product {n = suc _} F₁ F₂
  = record
  { function
    = λ x → dependent-simple-bool-function-product
      (DependentSimpleBoolFunction.bool-function F₁ x)
      (DependentSimpleBoolFunction.bool-function F₂ x)
  }

