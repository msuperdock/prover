module Prover.Prelude.Nat where

open import Prover.Prelude.Decidable
  using (Decidable; no; yes)
open import Prover.Prelude.Equality
  using (_≡_; refl)
open import Prover.Prelude.Trichotomous
  using (Trichotomous; equal; greater; less)

open import Agda.Builtin.String
  using (String)
import Agda.Builtin.Nat as Builtin

-- ## Definition

open Builtin public using ()
  renaming (Nat to ℕ)

Nat
  : Set
Nat
  = ℕ

open ℕ public

-- ## Module

module Nat where

  open ℕ public

  open Builtin public
    using (_+_; _*_)

  -- ### Conversion

  postulate
    show
      : ℕ
      → String

  {-# FOREIGN GHC
    import Data.Text
      (pack)
  #-}

  {-# COMPILE GHC show
    = pack . show #-}

  -- ### Equality

  _≟_nat
    : Decidable ℕ
  zero ≟ zero nat
    = yes refl
  suc n₁ ≟ suc n₂ nat
    with n₁ ≟ n₂ nat
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl
    = yes refl
  zero ≟ suc _ nat
    = no (λ ())
  suc _ ≟ zero nat
    = no (λ ())
  
  -- ### Comparison

  data _<_nat
    : ℕ
    → ℕ
    → Set
    where
  
    z<s
      : {n : ℕ}
      → zero < suc n nat
  
    s<s
      : {n₁ n₂ : ℕ}
      → n₁ < n₂ nat
      → suc n₁ < suc n₂ nat
  
  compare
    : Trichotomous _<_nat
  compare zero zero
    = equal (λ ()) refl (λ ())
  compare zero (suc _)
    = less z<s (λ ()) (λ ())
  compare (suc _) zero
    = greater (λ ()) (λ ()) z<s
  compare (suc m) (suc n)
    with compare m n
  ... | less l ¬p ¬g
    = less (s<s l) (λ {refl → ¬p refl}) (λ {(s<s g) → ¬g g})
  ... | equal ¬l refl ¬g
    = equal (λ {(s<s l) → ¬l l}) refl (λ {(s<s g) → ¬g g})
  ... | greater ¬l ¬p g
    = greater (λ {(s<s l) → ¬l l}) (λ {refl → ¬p refl}) (s<s g)

  transitive
    : {n₁ n₂ n₃ : ℕ}
    → n₁ < n₂ nat
    → n₂ < n₃ nat
    → n₁ < n₃ nat
  transitive z<s (s<s p)
    = z<s
  transitive (s<s p) (s<s q)
    = s<s (transitive p q)

-- ## Exports

open Nat public
  using (_+_; _*_; _≟_nat; _<_nat)
open _<_nat public

