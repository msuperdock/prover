module Prover.Prelude.Any where

open import Prover.Prelude.Equal
  using (Equal; _≡_; refl; sub)
open import Prover.Prelude.Relation
  using (Decidable; no; yes)
open import Prover.Prelude.Retraction
  using (Retraction)

-- ## Definition

record Any'
  {A : Set}
  (B : A → Set)
  : Set
  where

  constructor

    any

  field

    {index}
      : A

    value
      : B index

Any
  = Any'

-- ## Module

module Any where

  open Any' public

  -- ### Equality

  module _
    {A : Set}
    where

    decidable
      : (B : A → Set)
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

  -- ### Retraction

  module _
    {A : Set}
    {B C : A → Set}
    where

    module AnyRetraction
      {A : Set}
      {B C : A → Set}
      (F : (x : A) → Retraction (B x) (C x))
      where
  
      to
        : Any B
        → Any C
      to (any {x} y)
        = any (Retraction.to (F x) y)
  
      from
        : Any C
        → Any B
      from (any {x} z)
        = any (Retraction.from (F x) z)
  
      to-from
        : (z : Any C)
        → to (from z) ≡ z
      to-from (any {x} z)
        = sub any (Retraction.to-from (F x) z)
  
    retraction
      : ((x : A) → Retraction (B x) (C x))
      → Retraction (Any B) (Any C)
    retraction F
      = record {AnyRetraction F}

