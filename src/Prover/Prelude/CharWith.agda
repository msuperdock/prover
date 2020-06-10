module Prover.Prelude.CharWith where

open import Prover.Prelude.Any1
  using (Any₁)
open import Prover.Prelude.Bool
  using (Bool; T; false; true)
open import Prover.Prelude.Char
  using (Char)
open import Prover.Prelude.Digit
  using (Digit; Digits; 0d; 1d; 2d; 3d; 4d; 5d; 6d; 7d; 8d; 9d)
open import Prover.Prelude.Empty
  using (⊥-elim)
open import Prover.Prelude.Equality
  using (_≡_; refl; rewrite')
open import Prover.Prelude.Fin
  using (suc; zero)
open import Prover.Prelude.Function
  using (_$_; const)
open import Prover.Prelude.Inspect
  using ([_]; inspect)
open import Prover.Prelude.Maybe
  using (Maybe; just; nothing)
open import Prover.Prelude.Nat
  using (ℕ)
open import Prover.Prelude.Retraction
  using (Retraction; retraction-compose)
open import Prover.Prelude.Unit
  using (tt)
open import Prover.Prelude.Vec
  using (Vec)

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

  from-char
    : (p : Char → Bool)
    → Char
    → Maybe (CharWith p)
  from-char p c
    with p c | inspect p c
  ... | false | _
    = nothing
  ... | true | [ q ]
    = just (char-with c (rewrite' T q tt))

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
      = char-with c tt
  
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
      = ⊥-elim p
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
    : Retraction (Any₁ (Vec (CharWith Char.is-digit))) ℕ
  retraction-digits
    = retraction-compose Digits.retraction
    $ Any₁.retraction 
    $ Vec.retraction
    $ retraction-digit

  to-nat
    : Any₁ (Vec (CharWith Char.is-digit))
    → ℕ
  to-nat
    = Retraction.to retraction-digits

