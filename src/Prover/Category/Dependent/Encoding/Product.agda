module Prover.Category.Dependent.Encoding.Product where

open import Prover.Category.Chain
  using (ChainCategory)
open import Prover.Category.Dependent
  using (DependentCategory)
open import Prover.Category.Dependent.Encoding
  using (DependentEncoding)
open import Prover.Category.Dependent.Product
  using (dependent-category-product)
open import Prover.Category.Encoding.Product
  using (encoding-product)
open import Prover.Prelude

-- ## Types

dependent-encoding-product
  : {n : ℕ}
  → {C : ChainCategory n}
  → {C₁' C₂' : DependentCategory C}
  → {A₁ A₂ : Set}
  → DependentEncoding C₁' A₁
  → DependentEncoding C₂' A₂
  → DependentEncoding
    (dependent-category-product C₁' C₂')
    (A₁ × A₂)

-- ## Definitions

dependent-encoding-product {n = zero} e₁ e₂
  = encoding-product e₁ e₂

dependent-encoding-product {n = suc _} e₁ e₂
  = record
  { encoding
    = λ x → dependent-encoding-product
      (DependentEncoding.encoding e₁ x)
      (DependentEncoding.encoding e₂ x)
  }

