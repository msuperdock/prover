module Prover.Prelude.Char where
  
open import Prover.Prelude.Bool
  using (Bool; T; not)
open import Prover.Prelude.Decidable
  using (Dec; Decidable; no; yes)
open import Prover.Prelude.Digit
  using (Digit; 0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)
open import Prover.Prelude.Equality
  using (_≡_; from-homogeneous; refl; to-homogeneous)
open import Prover.Prelude.Fin
  using (suc; zero)
open import Prover.Prelude.Function
  using (_∘_)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (_≟_nat)
open import Prover.Prelude.Unit
  using (tt)

import Agda.Builtin.Char as Builtin
import Agda.Builtin.Char.Properties as Properties

open Builtin using ()
  renaming (primCharToNat to to-nat)
open Properties using ()
  renaming (primCharToNatInjective to to-nat-injective)

-- ## Definition

open Builtin public
  using (Char)

-- ## Module

module Char where

  -- ### Interface

  postulate

    is-space
      : Char
      → Bool

  {-# FOREIGN GHC
    import Data.Char
      (isSpace)
  #-}

  {-# COMPILE GHC is-space
    = isSpace #-}

  -- ### Conversion

  from-digit
    : Digit
    → Char
  from-digit 0d
    = '0'
  from-digit 1d
    = '1'
  from-digit 2d
    = '2'
  from-digit 3d
    = '3'
  from-digit 4d
    = '4'
  from-digit 5d
    = '5'
  from-digit 6d
    = '6'
  from-digit 7d
    = '7'
  from-digit 8d
    = '8'
  from-digit 9d
    = '9'

  to-digit
    : Char
    → Maybe Digit
  to-digit '0'
    = just 0d
  to-digit '1'
    = just 1d
  to-digit '2'
    = just 2d
  to-digit '3'
    = just 3d
  to-digit '4'
    = just 4d
  to-digit '5'
    = just 5d
  to-digit '6'
    = just 6d
  to-digit '7'
    = just 7d
  to-digit '8'
    = just 8d
  to-digit '9'
    = just 9d
  to-digit _
    = nothing
  
  is-digit
    : Char
    → Bool
  is-digit
    = Maybe.is-just ∘ to-digit

  IsDigit
    : Char
    → Set
  IsDigit c
    = T (is-digit c)

  is-digit?
    : (c : Char)
    → Dec (IsDigit c)
  is-digit? c
    = Bool.to-dec (is-digit c)

  is-digit-from-digit
    : (d : Digit)
    → T (is-digit (from-digit d))
  is-digit-from-digit 0d
    = tt
  is-digit-from-digit 1d
    = tt
  is-digit-from-digit 2d
    = tt
  is-digit-from-digit 3d
    = tt
  is-digit-from-digit 4d
    = tt
  is-digit-from-digit 5d
    = tt
  is-digit-from-digit 6d
    = tt
  is-digit-from-digit 7d
    = tt
  is-digit-from-digit 8d
    = tt
  is-digit-from-digit 9d
    = tt

  -- ### Equality

  _≟_char
    : Decidable Char
  c₁ ≟ c₂ char
    with to-nat c₁ ≟ to-nat c₂ nat
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes p
    = yes (from-homogeneous (to-nat-injective c₁ c₂ (to-homogeneous p)))
  
-- ## Exports

open Char public
  using (_≟_char)
