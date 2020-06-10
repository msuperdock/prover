module Prover.Prelude.List where

open import Prover.Prelude.Any
  using (Any; any)
open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (Equal; _≡_; refl)
open import Prover.Prelude.Nat
  using (ℕ)
open import Prover.Prelude.Vec
  using (Vec; []; _∷_)

import Agda.Builtin.List as Builtin

-- ## Definition

List
  : Set
  → Set
List
  = Builtin.List

open Builtin.List public

-- ## Module

module List where

  open Builtin.List public

  -- ### Interface

  map
    : {A B : Set}
    → (A → B)
    → List A
    → List B
  map f []
    = []
  map f (x ∷ xs)
    = f x ∷ map f xs

  append
    : {A : Set}
    → List A
    → List A
    → List A
  append [] ys
    = ys
  append (x ∷ xs) ys
    = x ∷ append xs ys

  concat
    : {A : Set}
    → List (List A)
    → List A
  concat []
    = []
  concat (xs ∷ xss)
    = append xs (concat xss)

  -- ### Construction

  module _
    {A : Set}
    where

    snoc
      : List A
      → A
      → List A
    snoc [] y
      = y ∷ []
    snoc (x ∷ xs) y
      = x ∷ snoc xs y

  -- ### Conversion

  module _
    {A : Set}
    where

    from-vec
      : {n : ℕ}
      → Vec A n
      → List A
    from-vec []
      = []
    from-vec (x ∷ xs)
      = x ∷ from-vec xs
  
    to-vec
      : List A
      → Any (Vec A)
    to-vec []
      = any []
    to-vec (x ∷ xs)
      with to-vec xs
    ... | any xs'
      = any (x ∷ xs')

  -- ### Equality

  module _
    {A : Set}
    where

    cons-eq
      : {x₁ x₂ : A}
      → {xs₁ xs₂ : List A}
      → x₁ ≡ x₂
      → xs₁ ≡ xs₂
      → Equal (List A) (List A) (x₁ ∷ xs₁) (x₂ ∷ xs₂)
    cons-eq refl refl
      = refl

    decidable
      : Decidable A
      → Decidable (List A)
  
    decidable _ [] []
      = yes refl
    decidable p (x₁ ∷ xs₁) (x₂ ∷ xs₂)
      with p x₁ x₂ | decidable p xs₁ xs₂
    ... | no ¬q | _
      = no (λ {refl → ¬q refl})
    ... | _ | no ¬q
      = no (λ {refl → ¬q refl})
    ... | yes refl | yes refl
      = yes refl
    
    decidable _ [] (_ ∷ _)
      = no (λ ())
    decidable _ (_ ∷ _) []
      = no (λ ())

  -- ### Properties

  module _
    {A : Set}
    where

    from-vec-to-vec
      : (xs : List A)
      → from-vec (Any.value (to-vec xs)) ≡ xs
    from-vec-to-vec []
      = refl
    from-vec-to-vec (x ∷ xs)
      = cons-eq refl (from-vec-to-vec xs)

