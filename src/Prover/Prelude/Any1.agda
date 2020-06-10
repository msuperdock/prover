module Prover.Prelude.Any1 where

open import Prover.Prelude.Any
  using (Any)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.Nat
  using (ℕ; suc)
open import Prover.Prelude.Retraction
  using (Retraction)

-- ## Definition

Any₁
  : (ℕ → Set)
  → Set
Any₁ A
  = Any (A ∘ suc)

-- ## Module

module Any₁ where

  -- ### Retraction

  retraction
    : {A B : ℕ → Set}
    → ((n : ℕ) → Retraction (A n) (B n))
    → Retraction (Any₁ A) (Any₁ B)
  retraction f
    = Any.retraction (f ∘ suc)

