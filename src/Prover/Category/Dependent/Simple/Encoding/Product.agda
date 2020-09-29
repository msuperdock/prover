module Prover.Category.Dependent.Simple.Encoding.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent.Encoding.Product
  using (dependent-encoding-product)
open import Prover.Category.Dependent.Encoding.Unit
  using (dependent-encoding-unit)
open import Prover.Category.Dependent.Simple
  using (DependentSimpleCategory)
open import Prover.Category.Dependent.Simple.Encoding
  using (DependentSimpleEncoding)
open import Prover.Category.Dependent.Simple.Encoding.Convert
  using (dependent-encoding-simple)
open import Prover.Category.Dependent.Simple.Product
  using (dependent-simple-category-product)
open import Prover.Prelude

-- ## DependentSimpleEncoding

dependent-simple-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentSimpleCategory C}
  → {A₁ A₂ : Set}
  → DependentSimpleEncoding C₁' A₁
  → DependentSimpleEncoding C₂' A₂
  → DependentSimpleEncoding
    (dependent-simple-category-product C₁' C₂')
    (A₁ × A₂)
dependent-simple-encoding-product e₁ e₂
  = dependent-encoding-simple
  $ dependent-encoding-product
    (dependent-encoding-unit e₁)
    (dependent-encoding-unit e₂)

