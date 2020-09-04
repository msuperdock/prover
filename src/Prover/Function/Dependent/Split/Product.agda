module Prover.Function.Dependent.Split.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Product
  using (dependent-category-product)
open import Prover.Function.Dependent.Split
  using (DependentSplitFunction; cons; dependent-split-function₀; nil)
open import Prover.Function.Split.Product
  using (split-function-product)
open import Prover.Prelude

-- ## DependentSplitFunction

dependent-split-function-product
  : {A₁ A₂ : Set}
  → {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → DependentSplitFunction A₁ C₁'
  → DependentSplitFunction A₂ C₂'
  → DependentSplitFunction
    (A₁ × A₂)
    (dependent-category-product C₁' C₂')
dependent-split-function-product {n = zero} F₁ F₂
  = nil
    (split-function-product
      (dependent-split-function₀ F₁)
      (dependent-split-function₀ F₂))
dependent-split-function-product {n = suc _} F₁ F₂
  = cons
    (λ x → dependent-split-function-product 
      (DependentSplitFunction.tail F₁ x)
      (DependentSplitFunction.tail F₂ x))

