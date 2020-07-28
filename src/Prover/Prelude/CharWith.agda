module Prover.Prelude.CharWith where

open import Prover.Prelude.Bool
  using (Bool; T; true)
open import Prover.Prelude.Char
  using (Char)
open import Prover.Prelude.Digit
  using (module Digits; Digit; 0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equal
  using (_≡_; refl)
open import Prover.Prelude.Function
  using (_$_; const)
open import Prover.Prelude.List1
  using (List₁)
open import Prover.Prelude.Maybe
  using (just; nothing)
open import Prover.Prelude.Nat
  using (ℕ)
open import Prover.Prelude.Retraction
  using (Retraction; retraction-compose)

-- ## Definition

module _CharWith where

  record CharWith
    (p : Char → Bool)
    : Set
    where
  
    constructor
    
      char-with
  
    field
    
      char
        : Char
  
      IsValid
        : T (p char)

CharWith
  : (Char → Bool)
  → Set
CharWith
  = _CharWith.CharWith

open _CharWith public
  using (char-with)

-- ## Module

module CharWith where

  -- ### Characters

  open _CharWith.CharWith public

  module CharWithRetraction where
  
    to
      : CharWith (const true)
      → Char
    to
      = char
    
    from
      : Char
      → CharWith (const true)
    from c
      = char-with c refl
  
    to-from
      : (c : Char)
      → to (from c) ≡ c
    to-from _
      = refl
  
  retraction
    : Retraction (CharWith (const true)) Char
  retraction
    = record {CharWithRetraction}

  -- ### Digits

  module CharWithRetractionDigit where

    to
      : CharWith Char.is-digit
      → Digit
    to (char-with c p)
      with Char.to-digit c
    ... | nothing
      = ⊥-elim (Bool.false≢true p)
    ... | just n
      = n

    from
      : Digit
      → CharWith Char.is-digit
    from d
      = char-with (Char.from-digit d) (Char.is-digit-from-digit d)

    to-from
      : (d : Digit)
      → to (from d) ≡ d
    to-from 0d
      = refl
    to-from 1d
      = refl
    to-from 2d
      = refl
    to-from 3d
      = refl
    to-from 4d
      = refl
    to-from 5d
      = refl
    to-from 6d
      = refl
    to-from 7d
      = refl
    to-from 8d
      = refl
    to-from 9d
      = refl

  retraction-digit
    : Retraction (CharWith Char.is-digit) Digit
  retraction-digit
    = record {CharWithRetractionDigit}

  retraction-digits
    : Retraction (List₁ (CharWith Char.is-digit)) ℕ
  retraction-digits
    = retraction-compose Digits.retraction
    $ List₁.retraction 
    $ retraction-digit

