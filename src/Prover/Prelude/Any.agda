module Prover.Prelude.Any where

open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (_≡_; refl)
open import Prover.Prelude.Retraction
  using (Retraction)

-- ## Definition

module _Any where

  record Any
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
  : {A : Set}
  → (A → Set)
  → Set
Any
  = _Any.Any

open _Any public
  using (any)

-- ## Module

module Any where

  open _Any.Any public

  -- ### Interface

  module _
    {A : Set}
    {B C : A → Set}
    where

    map
      : ({x : A} → B x → C x)
      → Any B
      → Any C
    map f (any y)
      = any (f y)

  -- ### Equality

  module _
    {A : Set}
    {B : A → Set}
    where

    decidable
      : Decidable A
      → ({x : A} → Decidable (B x))
      → Decidable (Any B)
    decidable p q (any {x₁} y₁) (any {x₂} y₂)
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
      (f : (x : A) → Retraction (B x) (C x))
      where
  
      to
        : Any B
        → Any C
      to (any {x} y)
        = any (Retraction.to (f x) y)
  
      from
        : Any C
        → Any B
      from (any {x} z)
        = any (Retraction.from (f x) z)
  
      to-from
        : (z : Any C)
        → to (from z) ≡ z
      to-from (any {x} z)
        with Retraction.to (f x) (Retraction.from (f x) z)
        | Retraction.to-from (f x) z
      ... | _ | refl
        = refl
  
    retraction
      : ((x : A) → Retraction (B x) (C x))
      → Retraction (Any B) (Any C)
    retraction f
      = record {AnyRetraction f}

