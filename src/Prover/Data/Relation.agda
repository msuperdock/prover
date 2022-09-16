module Prover.Data.Relation where

open import Prover.Data.Empty
  using (⊥-elim)
open import Prover.Data.Equal
  using (Equal; sym; trans)

import Data.Relation
  as Relation'

open Relation' public
  using (Decidable; Relation; τ₁; τ₂; τ₃; no; yes)

-- ## Relation

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

Dec
  = Relation'.Dec

module Dec where

  recompute
    : {A : Set}
    → Dec A
    → .A
    → A
  recompute (no ¬p) p
    = ⊥-elim (¬p p)
  recompute (yes p) _
    = p

module Decidable where

  map
    : {A B : Set}
    → (f : A → B)
    → (R : Relation B)
    → Decidable R
    → Decidable (Relation.map f R)
  map f _ d x₁ x₂
    = d (f x₁) (f x₂)

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

