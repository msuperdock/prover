module Prover.Data.Token where

open import Prover.Prelude

open List
  using ([]; _∷_)

-- ## Definition

module _Token where

  is-valid
    : List Char
    → Bool
  is-valid []
    = false
  is-valid (c ∷ cs)
    = not (Char.is-space c) ∨ is-valid cs

  IsValid
    : List Char
    → Set
  IsValid cs
    = T (is-valid cs)

  record Token
    : Set
    where
  
    constructor
    
      token

    field
  
      characters
        : List Char
  
      .valid
        : T (is-valid characters)

    length
      : ℕ
    length
      = List.length characters

Token
  : Set
Token
  = _Token.Token

open _Token public
  using (token)

-- ## Module

module Token where

  open _Token public
    using (IsValid; token)
  open _Token.Token public

  -- ### Interface

  -- The first non-space index.
  index
    : (t : Token)
    → Fin (length t)
  index (token (c ∷ cs) v)
    with Char.is-space c
  ... | false
    = zero
  ... | true
    = suc (index (token cs v))

  -- ### Equality
  
  _≟_tkn
    : Decidable (Equal Token)
  token cs₁ _ ≟ token cs₂ _ tkn
    with List.decidable _≟_char cs₁ cs₂
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl
    = yes refl
  
-- ## Exports

open Token public
  using (_≟_tkn)

