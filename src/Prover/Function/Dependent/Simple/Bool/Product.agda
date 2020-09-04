module Prover.Function.Dependent.Simple.Bool.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Function.Bool.Product
  using (bool-function-product)
open import Prover.Function.Dependent.Simple.Bool
  using (DependentSimpleBoolFunction; cons; dependent-simple-bool-function₀;
    nil)
open import Prover.Prelude

-- ## DependentSimpleBoolFunction

dependent-simple-bool-function-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → DependentSimpleBoolFunction C₁'
  → DependentSimpleBoolFunction C₂'
  → DependentSimpleBoolFunction
    (dependent-simple-category-product C₁' C₂')
dependent-simple-bool-function-product
  {n = zero} F₁ F₂
  = nil
    (bool-function-product
      (dependent-simple-bool-function₀ F₁)
      (dependent-simple-bool-function₀ F₂))
dependent-simple-bool-function-product
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-simple-bool-function-product
      (DependentSimpleBoolFunction.tail F₁ x)
      (DependentSimpleBoolFunction.tail F₂ x))

