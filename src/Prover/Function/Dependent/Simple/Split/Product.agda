module Prover.Function.Dependent.Simple.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Function.Dependent.Simple.Split
  using (DependentSimpleSplitFunction; cons; dependent-simple-split-function₀;
    nil)
open import Prover.Function.Split.Product
  using (split-function-product)
open import Prover.Prelude

-- ## DependentSimpleSplitFunction

dependent-simple-split-function-product
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → DependentSimpleSplitFunction A₁ C₁'
  → DependentSimpleSplitFunction A₂ C₂'
  → DependentSimpleSplitFunction
    (A₁ × A₂)
    (dependent-simple-category-product C₁' C₂')
dependent-simple-split-function-product
  {n = zero} F₁ F₂
  = nil
    (split-function-product
      (dependent-simple-split-function₀ F₁)
      (dependent-simple-split-function₀ F₂))
dependent-simple-split-function-product
  {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-simple-split-function-product 
      (DependentSimpleSplitFunction.tail F₁ x)
      (DependentSimpleSplitFunction.tail F₂ x))

