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

  retraction
    : Retraction (TextWith (const true)) Text
  retraction
    = Any₁.retraction (Vec.retraction CharWith.retraction)

