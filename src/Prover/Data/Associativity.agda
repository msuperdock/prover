module Prover.Data.Associativity where

open import Prover.Prelude

-- ## Definition

module _Associativity where

  data Associativity
    : Set
    where
  
    none
      : Associativity

    left
      : Associativity
  
    right
      : Associativity

Associativity
  : Set
Associativity
  = _Associativity.Associativity

-- ## Module

module Associativity where
  
  open _Associativity.Associativity public

  _≟_ass
    : Decidable Associativity
  none ≟ none ass
    = yes refl
  left ≟ left ass
    = yes refl
  right ≟ right ass
    = yes refl

  none ≟ left ass
    = no (λ ())
  none ≟ right ass
    = no (λ ())
  left ≟ none ass
    = no (λ ())
  left ≟ right ass
    = no (λ ())
  right ≟ none ass
    = no (λ ())
  right ≟ left ass
    = no (λ ())

-- ## Exports

open Associativity public
  using (_≟_ass)

