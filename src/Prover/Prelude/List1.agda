module Prover.Prelude.List1 where

open import Prover.Prelude.Any
  using (Any)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.Nat
  using (suc)
open import Prover.Prelude.Retraction
  using (Retraction)
open import Prover.Prelude.Vec
  using (Vec)

-- ## Definition

List₁
  : Set
  → Set
List₁ A
  = Any (Vec A ∘ suc)

-- ## Module

module List₁ where

  retraction
    : {A B : Set}
    → Retraction A B
    → Retraction (List₁ A) (List₁ B)
  retraction F
    = Any.retraction (Vec.retraction F ∘ suc)

