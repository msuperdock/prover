module Prover.Category.Simple.Product where

open import Prover.Category.Simple
  using (PartialFunction)
open import Prover.Prelude

-- ## PartialFunction

partial-function-product
  : {A₁ A₂ B₁ B₂ : Set}
  → PartialFunction A₁ B₁
  → PartialFunction A₂ B₂
  → PartialFunction (A₁ × A₂) (B₁ × B₂)
partial-function-product f₁ f₂ (x₁ , x₂)
  with f₁ x₁ | f₂ x₂
... | nothing | _
  = nothing
... | _ | nothing
  = nothing
... | just y₁ | just y₂
  = just (y₁ , y₂)

