module Prover.Data.Token where

open import Prover.Data.Bool
  using (Bool; T; _∨_; false; not; true)
open import Prover.Data.Char
  using (Char; _≟_char)
open import Prover.Data.Equal
  using (Equal; refl)
open import Prover.Data.Fin
  using (Fin; suc; zero)
open import Prover.Data.List
  using (List; []; _∷_)
open import Prover.Data.Nat
  using (ℕ)
open import Prover.Data.Relation
  using (Decidable; no; yes)

-- ## Definition

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

record Token'
  : Set
  where

  constructor
  
    token

  field

    characters
      : List Char

    .valid
      : IsValid characters

Token
  = Token'

-- ## Module

module Token where

  open Token' public

  -- ### Interface

  length
    : Token
    → ℕ
  length t
    = List.length (characters t)

  index'
    : (cs : List Char)
    → .(T (is-valid cs))
    → Fin (List.length cs)
  index' (c ∷ cs) p
    with Char.is-space c
  ... | false
    = zero
  ... | true
    = suc (index' cs p)

  -- The first non-space index.
  index
    : (t : Token)
    → Fin (length t)
  index (token cs p)
    = index' cs p

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

