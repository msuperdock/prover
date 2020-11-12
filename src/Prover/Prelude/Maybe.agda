module Prover.Prelude.Maybe where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Equal
  using (_≡_; _≢_; refl)
open import Prover.Prelude.Sigma
  using (Σ; _,_)

-- ## Definition

data Maybe'
  (A : Set)
  : Set
  where

  nothing
    : Maybe' A

  just
    : A
    → Maybe' A

{-# COMPILE GHC Maybe' = data Maybe
  ( Nothing
  | Just
  )
#-}

Maybe
  = Maybe'

-- ## Module

module Maybe where

  open Maybe' public

  -- ### Interface

  is-just
    : {A : Set}
    → Maybe A
    → Bool
  is-just nothing
    = false
  is-just (just _)
    = true

  maybe
    : {A B : Set}
    → Maybe A
    → B
    → (A → B)
    → B
  maybe nothing n _
    = n
  maybe (just x) _ j
    = j x
  
  map
    : {A B : Set}
    → (A → B)
    → Maybe A
    → Maybe B
  map _ nothing
    = nothing
  map f (just x)
    = just (f x)

  -- ### Properties

  nothing≢just
    : {A : Set}
    → {x : A}
    → nothing ≢ just x
  nothing≢just ()

  just≢nothing
    : {A : Set}
    → {x : A}
    → just x ≢ nothing
  just≢nothing ()

  just-injective
    : {A : Set}
    → {x₁ x₂ : A}
    → just x₁ ≡ just x₂
    → x₁ ≡ x₂
  just-injective refl
    = refl

  map-nothing
    : {A B : Set}
    → (f : A → B)
    → (x : Maybe A)
    → map f x ≡ nothing
    → x ≡ nothing
  map-nothing _ nothing _
    = refl

  map-just
    : {A B : Set}
    → {y : B}
    → (f : A → B)
    → (x : Maybe A)
    → map f x ≡ just y
    → z ∈ A
    × p ∈ x ≡ just z
    × f z ≡ y
  map-just _ (just x) refl
    = (x , refl , refl)

-- ## Exports

open Maybe public
  using (maybe)

