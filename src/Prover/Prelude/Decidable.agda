module Prover.Prelude.Decidable where

open import Prover.Prelude.Empty
  using (¬_; ⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_)

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
  : Set
  → Set
Decidable A
  = (x y : A)
  → Dec (x ≡ y)

recompute
  : {A : Set}
  → Dec A
  → .A
  → A
recompute (no ¬p) p
  = ⊥-elim (¬p p)
recompute (yes p) _
  = p

