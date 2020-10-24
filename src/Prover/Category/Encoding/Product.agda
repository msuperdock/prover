module Prover.Category.Encoding.Product where

open import Prover.Category.Encoding
  using (Encoding; split-function-encoding)
open import Prover.Function.Split.Product
  using (split-function-product)
open import Prover.Prelude

-- ## Encoding

encoding-product
  : {A₁ A₂ B₁ B₂ : Set}
  → Encoding A₁ B₁
  → Encoding A₂ B₂
  → Encoding (A₁ × A₂) (B₁ × B₂)
encoding-product e₁ e₂
  = split-function-encoding
  $ split-function-product
    (Encoding.split-function e₁)
    (Encoding.split-function e₂)

