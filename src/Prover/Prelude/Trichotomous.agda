module Prover.Prelude.Trichotomous where

open import Prover.Prelude.Empty
  using (¬_)
open import Prover.Prelude.Equality
  using (_≡_)

data Tri
  (P : Set)
  (Q : Set)
  (R : Set)
  : Set
  where

  less
    : P
    → ¬ Q
    → ¬ R
    → Tri P Q R

  equal
    : ¬ P
    → Q
    → ¬ R
    → Tri P Q R

  greater
    : ¬ P
    → ¬ Q
    → R
    → Tri P Q R

Trichotomous
  : {A : Set}
  → (A → A → Set)
  → Set
Trichotomous {A} _<_
  = (x y : A)
  → Tri (x < y) (x ≡ y) (y < x)

