module Prover.Data.Text where

open import Prover.Prelude

-- ## Definitions

Text
  : Set
Text
  = List₁ Char

TextWith
  : (Char → Bool)
  → Set
TextWith p
  = List₁ (CharWith p)

-- ## Module

module Text where

  _≟_txt
    : Decidable (Equal Text)
  _≟_txt
    = Any.decidable
      (λ n → Vec Char (suc n))
      _≟_nat
      (Vec.decidable _≟_char)

  retraction
    : Retraction
      (TextWith (const true))
      Text
  retraction
    = List₁.retraction CharWith.retraction

open Text public
  using (_≟_txt)

