module Prover.Prelude.Maybe where

open import Prover.Prelude.Bool
  using (Bool; false; true)
open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (Equal'; _≅_; _≡_; _≢_; refl)

-- ## Definition

module _Maybe where

  data Maybe
    (A : Set)
    : Set
    where
  
    nothing
      : Maybe A
  
    just
      : A
      → Maybe A
  
  {-# COMPILE GHC Maybe = data Maybe
    ( Nothing
    | Just
    )
  #-}

Maybe
  : Set
  → Set
Maybe
  = _Maybe.Maybe

open _Maybe.Maybe public

-- ## Module

module Maybe where

  open _Maybe.Maybe public

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

  -- ### Equality

  decidable
    : {A : Set}
    → Decidable A
    → Decidable (Maybe A)
  decidable _ nothing nothing
    = yes refl
  decidable _ nothing (just _)
    = no (λ ())
  decidable _ (just _) nothing
    = no (λ ())
  decidable _≟_ (just x₁) (just x₂)
    with x₁ ≟ x₂
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl
    = yes refl

  nothing-eq₂
    : {A B : Set}
    → {x₁ x₂ : A}
    → {y₁ y₂ : B}
    → (P : A → B → Set)
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → Equal' (Maybe (P x₁ y₁)) (Maybe (P x₂ y₂)) nothing nothing
  nothing-eq₂ _ refl refl
    = refl
  
  just-eq₂
    : {A B : Set}
    → {x₁ x₂ : A}
    → {y₁ y₂ : B}
    → (P : A → B → Set)
    → {p₁ : P x₁ y₁}
    → {p₂ : P x₂ y₂}
    → x₁ ≡ x₂
    → y₁ ≡ y₂
    → p₁ ≅ p₂
    → just p₁ ≅ just p₂
  just-eq₂ _ refl refl refl
    = refl

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

  just-injective'
    : {A : Set}
    → (B : A → Set)
    → {x₁ x₂ : A}
    → {y₁ : B x₁}
    → {y₂ : B x₂}
    → x₁ ≡ x₂
    → Equal'
      (Maybe (B x₁))
      (Maybe (B x₂))
      (just y₁)
      (just y₂)
    → y₁ ≅ y₂
  just-injective' _ refl refl
    = refl

-- ## Exports

open Maybe public
  using (maybe)

