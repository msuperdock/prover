module Prover.Data.Equal where

import Agda.Builtin.Equality
  as Builtin

import Data.Equal
  as Equal'

-- ## Definition

Equal
  = Equal'.Equal

open Equal' public
  using (_≡_; _≢_; refl)

open Builtin
  using () renaming
  ( _≡_
    to _≡'_
  ; refl
    to refl
  )

-- ## Module

module Equal where

  open Equal'.Equal public

  -- ### Conversion

  to-builtin
    : {A : Set}
    → {x₁ x₂ : A}
    → x₁ ≡ x₂
    → x₁ ≡' x₂
  to-builtin refl
    = refl

  from-builtin
    : {A : Set}
    → {x₁ x₂ : A}
    → x₁ ≡' x₂
    → x₁ ≡ x₂
  from-builtin refl
    = refl

  -- ### Rewrite

  rewrite₂
    : {A B : Set}
    → {x₁ x₂ : A}
    → {y₁ y₂ : B}
    → (P : A → B → Set)
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → P x₂ y₂
    → P x₁ y₁
  rewrite₂ _ refl refl p
    = p

-- ## Exports

open Equal public
  using (rewrite'; sub; sym; trans)

