module Prover.Category.Dependent.Simple.Partial.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Category.Dependent.Simple.Partial
  using (DependentSimplePartialFunction)
open import Prover.Function.Dependent
  using (DependentSet)
open import Prover.Function.Dependent.Product
  using (dependent-set-product)
open import Prover.Function.Partial.Product
  using (partial-function-product)
open import Prover.Prelude

-- ## Types

dependent-simple-partial-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → {D₁' D₂' : DependentSet C}
  → DependentSimplePartialFunction C₁' D₁'
  → DependentSimplePartialFunction C₂' D₂'
  → DependentSimplePartialFunction
    (dependent-simple-category-product C₁' C₂')
    (dependent-set-product D₁' D₂')

-- ## Definitions

dependent-simple-partial-function-product {n = zero} F₁ F₂
  = partial-function-product F₁ F₂

dependent-simple-partial-function-product {n = suc _} F₁ F₂
  = record
  { partial-function
    = λ x → dependent-simple-partial-function-product
      (DependentSimplePartialFunction.partial-function F₁ x)
      (DependentSimplePartialFunction.partial-function F₂ x)
  }

