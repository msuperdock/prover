module Prover.Data.Bool where

open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Function
  using (_∘_)
open import Prover.Data.Relation
  using (Dec; Decidable; Relation; Symmetric; Transitive; no; yes)

import Data.Bool
  as Bool'

-- ## Definition

Bool
  = Bool'.Bool

open Bool' public
  using (false; true)

-- ## Module

module Bool where

  open Bool'.Bool public

  -- ### Equality

  _≟_bool
    : Decidable (Equal Bool)
  false ≟ false bool
    = yes refl
  true ≟ true bool
    = yes refl
  false ≟ true bool
    = no (λ ())
  true ≟ false bool
    = no (λ ())

  -- ### Conversion

  to-dec
    : (x : Bool)
    → Dec (T x)
  to-dec false
    = no (λ ())
  to-dec true
    = yes refl

  from-dec
    : {A : Set}
    → Dec A
    → Bool
  from-dec (no _)
    = false
  from-dec (yes _)
    = true

  from-dec-true
    : {A : Set}
    → (d : Dec A)
    → A
    → T (from-dec d)
  from-dec-true (no ¬x) x
    = ⊥-elim (¬x x)
  from-dec-true (yes _) _
    = refl

  from-decidable
    : {A : Set}
    → {R : Relation A}
    → Decidable R
    → A
    → A
    → Bool
  from-decidable d x₁ x₂
    = from-dec (d x₁ x₂)

  from-decidable-true
    : {A : Set}
    → {R : Relation A}
    → (d : Decidable R)
    → (x₁ x₂ : A)
    → R x₁ x₂
    → T (from-decidable d x₁ x₂)
  from-decidable-true d x₁ x₂
    = from-dec-true (d x₁ x₂)

  -- ### Uniqueness

  Unique
    : {A : Set}
    → Relation A
    → (A → Bool)
    → Set
  Unique {A = A} R f
    = (x₁ x₂ : A)
    → T (f x₁)
    → T (f x₂)
    → R x₁ x₂

  module Unique where

    decidable
      : {A : Set}
      → {R : Relation A}
      → Symmetric R
      → Transitive R
      → (d : Decidable R)
      → (x : A)
      → Unique R (from-decidable d x)
    decidable s t d x x₁ x₂ _ _
      with d x x₁
      | d x x₂
    ... | yes r₁ | yes r₂
      = t x₁ x x₂ (s x x₁ r₁) r₂

    equal
      : {A : Set}
      → (d : Decidable (Equal A))
      → (x : A)
      → Unique (Equal A) (from-decidable d x)
    equal {A = A}
      = decidable
        (Symmetric.equal A)
        (Transitive.equal A)

    map
      : {A B : Set}
      → (f : A → B)
      → (R : Relation B)
      → (g : B → Bool)
      → Unique R g
      → Unique (Relation.map f R) (g ∘ f)
    map f _ _ u x₁ x₂
      = u (f x₁) (f x₂)

  -- ### Properties
  
  ∧-elimination-left
    : {x y : Bool}
    → T (x ∧ y)
    → T x
  ∧-elimination-left {x = false} p
    = p
  ∧-elimination-left {x = true} _
    = refl
  
  ∧-elimination-right
    : {x y : Bool}
    → T (x ∧ y)
    → T y
  ∧-elimination-right {x = true} p
    = p
  
-- ## Exports

open Bool public
  using (Unique; F; T; _∨_; _∧_; _≟_bool; not)

