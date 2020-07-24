module Prover.Prelude.Equality where

open import Agda.Builtin.Equality
  using (refl)
open import Prover.Prelude.Empty
  using (¬_)

open Agda.Builtin.Equality using () renaming
  ( _≡_
    to _≡'_
  )

-- ## Definition

infix 4 _≅_
infix 4 _≡_
infix 4 _≢_

data _≅_
  {A : Set}
  (x : A)
  : {B : Set}
  → B
  → Set
  where

    refl
      : x ≅ x

Equal
  : (A : Set)
  → A
  → A
  → Set
Equal _ x₁ x₂
  = x₁ ≅ x₂

Equal'
  : (A B : Set)
  → A
  → B
  → Set
Equal' _ _ x₁ x₂
  = x₁ ≅ x₂

_≡_
  : {A : Set}
  → A
  → A
  → Set
x₁ ≡ x₂
  = x₁ ≅ x₂

_≢_
  : {A : Set}
  → A
  → A
  → Set
x₁ ≢ x₂
  = ¬ x₁ ≡ x₂

-- ## Interface

sym
  : {A₁ A₂ : Set}
  → {x₁ : A₁}
  → {x₂ : A₂}
  → x₁ ≅ x₂
  → x₂ ≅ x₁
sym refl
  = refl

trans
  : {A₁ A₂ A₃ : Set}
  → {x₁ : A₁}
  → {x₂ : A₂}
  → {x₃ : A₃}
  → x₁ ≅ x₂
  → x₂ ≅ x₃
  → x₁ ≅ x₃
trans refl refl
  = refl

sub
  : {A B : Set}
  → {x₁ x₂ : A}
  → (P : A → B)
  → x₁ ≡ x₂
  → P x₁ ≡ P x₂
sub _ refl
  = refl

-- ## Conversion

from-homogeneous
  : {A : Set}
  → {x₁ x₂ : A}
  → x₁ ≡' x₂
  → x₁ ≡ x₂
from-homogeneous refl
  = refl

to-homogeneous
  : {A : Set}
  → {x₁ x₂ : A}
  → x₁ ≡ x₂
  → x₁ ≡' x₂
to-homogeneous refl
  = refl

-- ## Irrelevance

irrelevant
  : {A₁ A₂ : Set}
  → {x₁ : A₁}
  → {x₂ : A₂}
  → (p₁ p₂ : x₁ ≅ x₂)
  → p₁ ≡ p₂
irrelevant refl refl
  = refl

-- ## Rewrite

rewrite'
  : {A : Set}
  → {x₁ x₂ : A}
  → (P : A → Set)
  → x₁ ≡ x₂
  → P x₂
  → P x₁
rewrite' _ refl p
  = p

