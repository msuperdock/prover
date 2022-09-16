module Prover.Data.Associativity where

open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Relation
  using (Decidable; no; yes)

-- ## Definition

data Associativity'
  : Set
  where

  none
    : Associativity'

  left
    : Associativity'

  right
    : Associativity'

Associativity
  = Associativity'

-- ## Module

module Associativity where
  
  open Associativity' public

  _≟_ass
    : Decidable (Equal Associativity)
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

