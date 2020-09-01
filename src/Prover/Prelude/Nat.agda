module Prover.Prelude.Nat where

open import Prover.Prelude.Equal
  using (Equal; refl)
open import Prover.Prelude.Relation
  using (Decidable; Trichotomous; τ₁; τ₂; τ₃; no; yes)

open import Agda.Builtin.String
  using (String)
import Agda.Builtin.Nat as Builtin

-- ## Definition

open Builtin public using ()
  renaming (Nat to ℕ)

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
    : Decidable (Equal ℕ)
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
      : {n₂ : ℕ}
      → zero < suc n₂ nat
  
    s<s
      : {n₁ n₂ : ℕ}
      → n₁ < n₂ nat
      → suc n₁ < suc n₂ nat
  
  compare
    : Trichotomous _<_nat
  compare zero zero
    = τ₂ (λ ()) refl (λ ())
  compare zero (suc _)
    = τ₁ z<s (λ ()) (λ ())
  compare (suc _) zero
    = τ₃ (λ ()) (λ ()) z<s
  compare (suc m) (suc n)
    with compare m n
  ... | τ₁ l ¬p ¬g
    = τ₁ (s<s l) (λ {refl → ¬p refl}) (λ {(s<s g) → ¬g g})
  ... | τ₂ ¬l refl ¬g
    = τ₂ (λ {(s<s l) → ¬l l}) refl (λ {(s<s g) → ¬g g})
  ... | τ₃ ¬l ¬p g
    = τ₃ (λ {(s<s l) → ¬l l}) (λ {refl → ¬p refl}) (s<s g)

  <-trans
    : {n₁ n₂ n₃ : ℕ}
    → n₁ < n₂ nat
    → n₂ < n₃ nat
    → n₁ < n₃ nat
  <-trans z<s (s<s _)
    = z<s
  <-trans (s<s p₁) (s<s p₂)
    = s<s (<-trans p₁ p₂)

-- ## Exports

open Nat public
  using (_+_; _*_; _≟_nat)

