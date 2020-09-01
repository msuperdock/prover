module Prover.Function.Bool.Product where

open import Prover.Function.Bool
  using (BoolFunction)
open import Prover.Prelude

-- ## BoolFunction

bool-function-product
  : {A₁ A₂ : Set}
  → BoolFunction A₁
  → BoolFunction A₂
  → BoolFunction (A₁ × A₂)
bool-function-product f₁ f₂ (x₁ , x₂)
  = f₁ x₁ ∧ f₂ x₂

