module Prover.Prelude.Relation where

open import Prover.Prelude.Empty
  using (¬_; ⊥-elim)
open import Prover.Prelude.Equal
  using (Equal; _≡_; sym; trans)

-- ## Relation

Relation
  : Set
  → Set₁
Relation A
  = A
  → A
  → Set

module Relation where

  map
    : {A B : Set}
    → (A → B)
    → Relation B
    → Relation A
  map f R x₁ x₂
    = R (f x₁) (f x₂)

-- ## Symmetric

Symmetric
  : {A : Set}
  → Relation A
  → Set
Symmetric {A = A} R
  = (x₁ x₂ : A)
  → R x₁ x₂
  → R x₂ x₁

module Symmetric where

  equal
    : (A : Set)
    → Symmetric (Equal A)
  equal _ _ _
    = sym

  map
    : {A B : Set}
    → (f : A → B)
    → (R : Relation B)
    → Symmetric R
    → Symmetric (Relation.map f R)
  map f _ s x₁ x₂
    = s (f x₁) (f x₂)

-- ## Transitive

Transitive
  : {A : Set}
  → Relation A
  → Set
Transitive {A = A} R
  = (x₁ x₂ x₃ : A)
  → R x₁ x₂
  → R x₂ x₃
  → R x₁ x₃

module Transitive where

  equal
    : (A : Set)
    → Transitive (Equal A)
  equal _ _ _ _
    = trans

  map
    : {A B : Set}
    → (f : A → B)
    → (R : Relation B)
    → Transitive R
    → Transitive (Relation.map f R)
  map f _ t x₁ x₂ x₃
    = t (f x₁) (f x₂) (f x₃)

-- ## Decidable

data Dec
  (P : Set)
  : Set
  where

  yes
    : P
    → Dec P
  no
    : ¬ P
    → Dec P

Decidable
  : {A : Set}
  → Relation A
  → Set
Decidable {A = A} R
  = (x₁ x₂ : A)
  → Dec (R x₁ x₂)

module Decidable where

  map
    : {A B : Set}
    → (f : A → B)
    → (R : Relation B)
    → Decidable R
    → Decidable (Relation.map f R)
  map f _ d x₁ x₂
    = d (f x₁) (f x₂)

  recompute
    : {A : Set}
    → Dec A
    → .A
    → A
  recompute (no ¬p) p
    = ⊥-elim (¬p p)
  recompute (yes p) _
    = p

-- ## Trichotomous

data Tri
  (P₁ P₂ P₃ : Set)
  : Set
  where

  τ₁
    : P₁
    → ¬ P₂
    → ¬ P₃
    → Tri P₁ P₂ P₃

  τ₂
    : ¬ P₁
    → P₂
    → ¬ P₃
    → Tri P₁ P₂ P₃

  τ₃
    : ¬ P₁
    → ¬ P₂
    → P₃
    → Tri P₁ P₂ P₃

Trichotomous
  : {A : Set}
  → Relation A
  → Set
Trichotomous {A = A} R
  = (x₁ x₂ : A)
  → Tri (R x₁ x₂) (x₁ ≡ x₂) (R x₂ x₁)

-- ## Injective

Injective
  : {A B : Set}
  → Relation A
  → Relation B
  → (A → B)
  → Set
Injective {A = A} R S f
  = (x₁ x₂ : A)
  → S (f x₁) (f x₂)
  → R x₁ x₂

