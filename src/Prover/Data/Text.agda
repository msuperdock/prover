module Prover.Data.Text where

open import Prover.Prelude

-- ## Definitions

Text
  : Set
Text
  = Any₁ (Vec Char)

TextWith
  : (Char → Bool)
  → Set
TextWith p
  = Any₁ (Vec (CharWith p))

-- ## Module

module Text where

  _≟_txt
    : Decidable Text
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
    = Any₁.retraction
      (Vec.retraction
        CharWith.retraction)

open Text public
  using (_≟_txt)

