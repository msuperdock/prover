module Prover.Data.Any where

open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Relation
  using (Decidable; no; yes)

import Data.Any
  as Any'

-- ## Definition

Any
  = Any'.Any

open Any' public
  using (any)

-- ## Module

module Any where

  open Any'.Any public

  decidable
    : {A : Set}
    → (B : A → Set)
    → Decidable (Equal A)
    → ({x : A} → Decidable (Equal (B x)))
    → Decidable (Equal (Any B))
  decidable _ p q (any {x₁} y₁) (any {x₂} y₂)
    with p x₁ x₂
  ... | no ¬r
    = no (λ {refl → ¬r refl})
  ... | yes refl
    with q y₁ y₂
  ... | no ¬r
    = no (λ {refl → ¬r refl})
  ... | yes refl
    = yes refl

