module Prover.Data.Token where

open import Prover.Prelude

-- ## Definition

module _Token where

  is-valid
    : {n : ℕ}
    → Vec Char n
    → Bool
  is-valid []
    = false
  is-valid (c ∷ cs)
    = not (Char.is-space c) ∨ is-valid cs

  IsValid
    : {n : ℕ}
    → Vec Char n
    → Set
  IsValid cs
    = T (is-valid cs)

  record Token
    : Set
    where
  
    constructor
    
      token

    field
  
      {length}
        : ℕ
  
      characters
        : Vec Char length
  
      .valid
        : T (is-valid characters)

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
    : Decidable Token
  token {length = n₁} cs₁ _ ≟ token {length = n₂} cs₂ _ tkn
    with n₁ ≟ n₂ nat
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl
    with Vec.decidable _≟_char cs₁ cs₂
  ... | no ¬p
    = no (λ {refl → ¬p refl})
  ... | yes refl
    = yes refl
  
-- ## Exports

open Token public
  using (_≟_tkn)

