module Prover.Prelude.Sigma where

open import Prover.Prelude.Equal
  using (_≅_; _≡_; refl)
open import Prover.Prelude.Level
  using (Level; lmax)

import Agda.Builtin.Sigma as Builtin

-- ## Definition

Σ
  : {ℓ₁ ℓ₂ : Level}
  → (A₁ : Set ℓ₁)
  → (A₁ → Set ℓ₂)
  → Set (lmax ℓ₁ ℓ₂)
Σ
  = Builtin.Σ

infix 2 Σ

syntax Σ A₁ (λ x → A₂)
  = x ∈ A₁ × A₂

open Builtin public
  using (_,_)
open Builtin public using () renaming
  ( fst
    to π₁
  ; snd
    to π₂
  )

-- ## Module

module Sigma where

  -- ### Interface

  infixr 2 _×_

  _×_
    : Set
    → Set
    → Set
  A₁ × A₂
    = _ ∈ A₁ × A₂

  map
    : {A₁ : Set}
    → {A₂ B₂ : A₁ → Set}
    → ((x₁ : A₁) → A₂ x₁ → B₂ x₁)
    → Σ A₁ A₂
    → Σ A₁ B₂
  map f (x₁ , x₂)
    = (x₁ , f x₁ x₂)

  -- ### Equality

  comma-eq
    : {A₁ : Set}
    → {A₂ : A₁ → Set}
    → {x₁ y₁ : A₁}
    → {x₂ : A₂ x₁}
    → {y₂ : A₂ y₁}
    → x₁ ≡ y₁
    → x₂ ≅ y₂
    → (x₁ , x₂) ≡ (y₁ , y₂)
  comma-eq refl refl
    = refl

-- ## Exports

open Sigma public
  using (_×_)

