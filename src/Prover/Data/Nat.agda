module Prover.Data.Nat where

open import Agda.Builtin.String
  using (String)

open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Relation
  using (Decidable; no; yes)

import Data.Nat
  as Nat'

open Nat' public
  using (ℕ; suc; zero)

-- ## Module

module Nat where

  open Nat'.Nat public

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

  -- ### Comparison

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
  using (_≟_nat; _<_nat)

