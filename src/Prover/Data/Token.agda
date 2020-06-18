module Prover.Data.Token where

open import Prover.Category.Split.Base
  using (SplitFunction)
open import Prover.Data.Text
  using (Text)
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

  is-valid?
    : {n : ℕ}
    → (cs : Vec Char n)
    → Dec (IsValid cs)
  is-valid? cs
    = Bool.to-dec (is-valid cs)

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
    using (IsValid; token; is-valid; is-valid?)
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
  
  -- ### Split
  
  token-from-text
    : Text
    → Maybe Token
  token-from-text (any cs)
    with is-valid? cs
  ... | no _
    = nothing
  ... | yes v
    = just (token cs v)

  token-to-text
    : Token
    → Text
  token-to-text (token cs@(_ ∷ _) _)
    = any cs

  token-from-to-text
    : (t : Token)
    → token-from-text (token-to-text t) ≡ just t
  token-from-to-text (token cs@(_ ∷ _) v)
    with is-valid? cs
  ... | no ¬v
    = ⊥-elim (¬v v)
  ... | yes _
    = refl

  split-function
    : SplitFunction Text Token
  split-function
    = record
    { partial-function
      = token-from-text
    ; function
      = token-to-text
    ; valid
      = token-from-to-text
    }

-- ## Exports

open Token public
  using (_≟_tkn)

